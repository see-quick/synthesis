# author: Roman Andriushchenko
# co-author: Simon Stupinsky
import logging
import time
import z3

import operator
import stormpy

from dynasty.family_checkers.cegis import Synthesiser
from dynasty.family_checkers.quotientbased import LiftingChecker
from dynasty.jani.jani_quotient_builder import JaniQuotientBuilder, ThresholdSynthesisResult

logger = logging.getLogger(__file__)


def check_model(model, property_obj, quantitative=False):
    """Model check a model against a (quantitative) property."""
    raw_formula = property_obj.raw_formula
    formula = raw_formula
    if quantitative:
        formula = formula.clone()
        formula.remove_bound()

    result = stormpy.model_checking(model, formula)
    satisfied = result.at(model.initial_states[0])
    if quantitative:
        op = {
            stormpy.ComparisonType.LESS: operator.lt,
            stormpy.ComparisonType.LEQ: operator.le,
            stormpy.ComparisonType.GREATER: operator.gt,
            stormpy.ComparisonType.GEQ: operator.ge
        }[raw_formula.comparison_type]
        satisfied = op(satisfied, raw_formula.threshold_expr.evaluate_as_double())
    return satisfied, result


class Statistic:
    """General computation stats."""
    def __init__(self, method):
        self.method = method
        self.assignment = {}
        self.time = 0
        self.iterations = 0
        self.timer = None
        self.result = None
        self.toggle_timer()

    def toggle_timer(self):
        if self.timer is None:
            self.timer = time.time()
        else:
            self.time += time.time() - self.timer
            self.timer = None

    def finished(self, assignment, iterations):
        self.toggle_timer()
        self.result = assignment is not None
        self.assignment = {k: v.__str__() for (k, v) in assignment.items()} if assignment is not None else None
        self.iterations = iterations

    def __str__(self):
        return f"{round(self.time, 2)}, {self.iterations}, {self.result}"


class CEGISChecker(Synthesiser):
    """CEGIS wrapper."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.statistic = Statistic("CEGIS")

    def run(self):
        _, assignment, _ = self.run_feasibility()
        self.statistic.finished(assignment, self.stats.iterations)


class CEGARChecker(LiftingChecker):
    """CEGAR wrapper."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.statistic = Statistic("CEGAR")
        self.iterations = 0
        self.threshold = 0
        self.use_oracle = True
        self.new_options = None
        self.satisfying_assignment = None
        self.oracle = None

    def cegar_initialisation(self):
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes
        return [self.hole_options]

    def cegar_split_option(self, option, index=0):
        self.oracle.scheduler_color_analysis(index)
        return self._split_hole_options(option, self.oracle)

    def _analyse_option(self, option):
        if self.oracle is None:
            self.oracle = LiftingChecker._analyse_from_scratch(self, self._open_constants, option, set())
        else:
            LiftingChecker._analyse_sub_options(self, self.oracle, option)

    def cegar_analyse_option(self, option):
        self.iterations += 1
        logger.info(f"CEGAR: iteration {self.iterations}, analysing option {option}.")
        self._analyse_option(option)

        threshold_synthesis_results = self.oracle.decided(self.thresholds)

        if self._contains_unsat_result(threshold_synthesis_results):
            logger.debug("Unsatisfying.")
        else:
            undecided_indices = \
                [idx for idx, r in enumerate(threshold_synthesis_results) if r == ThresholdSynthesisResult.UNDECIDED]
            if undecided_indices:
                self._delete_sat_formulae(undecided_indices)
                logger.debug("Undecided.")
                self.new_options = self.cegar_split_option(option, undecided_indices[0])
            else:
                logger.debug("Satisfying.")
                self.satisfying_assignment = option.pick_one_in_family()

    def run_feasibility(self):
        if self.input_has_optimality_property():
            return self._run_optimal_feasibility()
        if self.input_has_restrictions():
            raise RuntimeError("Restrictions are not supported by quotient based approaches")

        hole_options = self.cegar_initialisation()

        while len(hole_options) > 0:
            option = hole_options.pop(0)
            self.cegar_analyse_option(option)
            if self.satisfying_assignment is not None:
                return self.satisfying_assignment
            if self.new_options is not None:
                hole_options = self.new_options + hole_options

        logger.info("No more options to explore.")
        return None

    def run(self):
        assignment = self.run_feasibility()
        self.statistic.finished(assignment, self.iterations)


class IntegratedStatistic(Statistic):
    """Base stats + region info + CE stats"""

    def __init__(self):
        super().__init__("Hybrid")
        self.region_stats = []
        self.iters = 0
        self.commands_old = 0
        self.commands_new = 0
        self.holes_old = 0
        self.holes_new = 0
        self.bound = None

    def new_counterexample(self, commands_old, commands_new, holes_old, holes_new):
        self.iters += 1
        self.commands_old += commands_old
        self.commands_new += commands_new
        self.holes_old += holes_old
        self.holes_new += holes_new

    def end_region(self, storm_stat):
        # average
        self.iters = max(1, self.iters)
        region_stat = (
            (
                self.bound,
                self.iters,
                self.commands_old / self.iters,
                self.commands_new / self.iters,
                self.holes_old / self.iters,
                self.holes_new / self.iters
            ), storm_stat
        )
        self.region_stats.append(region_stat)

    def __str__(self):
        s = super().__str__()
        for (region_stat, storm_stat) in self.region_stats:
            region_stat = [round(x, 3) if not isinstance(x, list) else x for x in region_stat]
            storm_stat = [round(x, 3) for x in storm_stat]
            # s += "> {} : {}\n".format(region_stat, storm_stat)
        return s


class IntegratedChecker(CEGISChecker, CEGARChecker):
    """Integrated checker."""

    # parameters are set before invocation
    cegar_iterations_limit = None
    expanded_per_iter = None

    def __init__(self):
        CEGISChecker.__init__(self)
        CEGARChecker.__init__(self)
        self.cegis_iterations = 0
        self.cegar_iterations = 0
        self.statistic = IntegratedStatistic()
        self.mdp = None
        self.mdp_mc_results = []
        self.allowed_to_split_options = True

    def initialise(self):
        CEGARChecker.initialise(self)
        CEGISChecker.initialise(self)

    def result_exists(self, hole_options):
        """Check whether a satisfying assignment has been obtained or all regions have been explored."""
        return (self.satisfying_assignment is not None) or (len(hole_options) == 0)

    def compose_result(self, hole_options):
        """
        Compose synthesis result: either satisfying assignment has been obtained or all regions have been explored.
        """
        if self.satisfying_assignment is not None:
            logger.info("Found satisfying assignment.")
            return self.satisfying_assignment
        if len(hole_options) == 0:
            logger.info("No more options.")
            return None

    def cegar_analyse_option(self, option):
        """Analyse region and store mdp data."""
        CEGARChecker.cegar_analyse_option(self, option)
        self.cegar_iterations += 1
        self.mdp = self.oracle.mdp_handling.mdp
        self.mdp_mc_results = [latest_result.result for latest_result in self.oracle.latest_results]

    def cegar_split_option(self, option, index=0):
        """Split option when allowed."""
        return super().cegar_split_option(option, index) if self.allowed_to_split_options else []

    def naive_stats(self, instance, all_conflicts=True):
        """Naive counterexample generation (for comparison)."""
        result, conflicts = self._verifier.naive_check(instance, all_conflicts, naive_stats=True)
        # TODO: How does this comparison of counter-examples for multiple properties?
        return sum([len(r) for r in result]), sum([len(c) for c in conflicts])

    def cegis_analyse_option(self, builder_options, option, mdp, mdp_results):
        """Analyse a region using provided mdp data to construct smaller counterexamples."""
        logger.info(f"CEGIS: analysing option {option}.")
        self.statistic.bound = [mdp_result.at(mdp.initial_states[0]) for mdp_result in mdp_results]

        # reset solver
        self.hole_options = option
        self._initialize_solver()

        # Prepare counter-example generator for each given property
        # TODO: Temporary ignore until will implement optimal synthesis for integrated method
        # assert len(self.properties) == len(mdp_results)
        counterexamples = []
        for prop, mdp_result in zip(self.properties, mdp_results):
            counterexamples.append(stormpy.SynthesisResearchCounterexample(
                IntegratedChecker.expanded_per_iter, prop.raw_formula, mdp, mdp_result
            ))

        while True:
            self.cegis_iterations += 1
            logger.info(f"CEGIS: iteration {self.cegis_iterations}.")

            # get satisfiable assignment
            solver_result = self.solver.check()
            if solver_result != z3.sat:
                logger.debug("No further instances to explore.")
                break
            sat_model = self.solver.model()

            logger.debug(f"Iteration: {self.stats.iterations} instantiating..")
            # Create an assignment for the holes ..
            hole_assignments = self._sat_model_to_constants_assignment(sat_model)
            # and construct instance ..
            instance = self.build_instance(hole_assignments)

            # construct and model check a DTMC
            dtmc = stormpy.build_sparse_model_with_options(instance, builder_options)
            assert len(dtmc.initial_states) == 1  # to avoid ambiguity
            assert dtmc.initial_states[0] == 0  # is implied by topological ordering
            logger.info(f"Built a DTMC with {dtmc.nr_states} states.")

            satisfied = []
            for index, prop in enumerate(self.properties):
                dtmc_sat, dtmc_result = check_model(dtmc, prop, quantitative=True)
                satisfied.append(dtmc_sat)
                if not dtmc_sat:
                    critical_edges = counterexamples[index].construct(dtmc, dtmc_result)
                    conflict = self.verifier.conflict_analysis(critical_edges)
                    clause = z3.Not(z3.And(
                        [var == sat_model[var] for var, hole in self.template_meta_vars.items() if hole in conflict]
                    ))
                    self.solver.add(clause)

            if all(satisfied):
                self.satisfying_assignment = hole_assignments
                break

        for ce in counterexamples:
            self.statistic.end_region(ce.stats)

    def run_feasibility(self):
        """Run feasibility synthesis."""
        assert not self.input_has_restrictions()

        # perform MDP model checking & extract bounds on reachability probability;
        # explore options (DFS) just before reaching the limit of mdp iterations
        # (or until all options are exhausted)
        logger.info("Initiating CEGAR phase.")
        hole_options = self.cegar_initialisation()

        logger.info("Analysing with splitting.")
        while (len(hole_options) > 0) and \
                (self.cegar_iterations + len(hole_options) < IntegratedChecker.cegar_iterations_limit):
            option = hole_options.pop(0)
            self.cegar_analyse_option(option)
            if self.satisfying_assignment is not None:
                break
            if self.new_options is not None:
                hole_options = self.new_options + hole_options  # DFS

        if self.result_exists(hole_options):
            return self.compose_result(hole_options)

        # process remaining options without splitting undecided ones:
        logger.info("Analysing with splitting.")
        self.allowed_to_split_options = False

        mdp_problems = []
        for option in hole_options:
            self.cegar_analyse_option(option)
            if self.satisfying_assignment is not None:
                break
            if self.new_options is not None:
                logger.info(f"Storing hole option {option} for CEGIS processing.")
                mdp_problems.append((option, self.mdp, self.mdp_mc_results))
        logger.info(
            f"MDP model checking finished after {self.cegar_iterations} iterations, "
            f"there are {len(mdp_problems)} areas to explore."
        )

        # precompute DTMC builder options
        builder_options = stormpy.BuilderOptions([p.raw_formula for p in self.properties])
        builder_options.set_build_with_choice_origins(True)
        builder_options.set_build_state_valuations(True)
        builder_options.set_add_overlapping_guards_label()

        # initiate CEGIS for each hole_option
        logger.info("Initiating CEGIS phase.")

        for (option, mdp, mdp_mc_results) in mdp_problems:
            self.cegis_analyse_option(builder_options, option, mdp, mdp_mc_results)
            if self.satisfying_assignment is not None:
                break

        return self.compose_result([])

    def run(self):
        assignment = self.run_feasibility()
        self.statistic.finished(assignment, str(self.cegar_iterations) + " - " + str(self.cegis_iterations))


class Research:
    """Entry point: execution setup."""
    def __init__(
            self, check_prerequisites, backward_cuts, sketch_path, allowed_path, property_path,
            optimality_path, constants, restrictions, restriction_path
    ):

        assert not check_prerequisites
        # assert not restrictions

        self.sketch_path = sketch_path
        self.allowed_path = allowed_path
        self.property_path = property_path
        self.optimality_path = optimality_path
        self.constants = constants
        self.restrictions = restrictions
        self.restriction_path = restriction_path
        self.backward_cuts = backward_cuts

        # import research.generator1
        # import research.generator2
        # workspace.generator2.run()

        workdir = "workspace/experiments"
        with open(f"{workdir}/parameters.txt", 'r') as f:
            values = [int(x) for x in f.readlines()]
            regime = values[0]
            limit = values[1]
            expanded = values[2]
        IntegratedChecker.cegar_iterations_limit = limit
        IntegratedChecker.expanded_per_iter = expanded

        stats = []

        if regime == 0:
            # stats.append(self.run_algorithm(CEGISChecker))
            # stats.append(self.run_algorithm(CEGARChecker))
            stats.append(self.run_algorithm(IntegratedChecker))
        elif regime == 1:
            # stats.append(self.run_algorithm(CEGISChecker))
            # stats.append(self.run_algorithm(CEGARChecker))
            stats.append(self.run_algorithm(IntegratedChecker))
        elif regime in [2, 3]:
            stats.append(self.run_algorithm(IntegratedChecker))
        else:
            assert None

        print("\n")
        for stat in stats:
            print(stat)

    def run_algorithm(self, algorithm_class):
        print("\n\n\n")
        print(algorithm_class.__name__)
        algorithm = algorithm_class()
        algorithm.load_sketch(
            self.sketch_path, self.property_path, optimality_path=self.optimality_path, constant_str=self.constants
        )
        algorithm.load_template_definitions(self.allowed_path)
        if self.restrictions:
            algorithm.load_restrictions(self.restriction_path)
        algorithm.initialise()
        algorithm.run()
        return algorithm.statistic
