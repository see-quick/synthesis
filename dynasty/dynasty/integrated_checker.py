# author: Roman Andriushchenko
import logging
import time
import z3

import operator
import stormpy

from dynasty.family_checkers.cegis import Synthesiser
from dynasty.family_checkers.quotientbased import LiftingChecker
from dynasty.jani.jani_quotient_builder import JaniQuotientBuilder, ThresholdSynthesisResult

logger = logging.getLogger(__file__)

# ------------------------------------------------------------------------------
# wrappers


def check_model(model, property, quantitative=False):
    """Model check a model against a (quantitative) property."""
    raw_formula = property.raw_formula
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


def readable_assignment(assignment):
    return {k: v.__str__() for (k, v) in assignment.items()} if assignment is not None else None


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
        self.assignment = readable_assignment(assignment)
        self.iterations = iterations

    def __str__(self):
        return "> {}: {} ({} iters, {} sec)\n".format(self.method, self.result, self.iterations, round(self.time, 2))


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
        self.threshold = float(self.thresholds[0])
        return [self.hole_options]

    def cegar_split_option(self, option):
        self.oracle.scheduler_color_analysis()
        return self._split_hole_options(option, self.oracle)

    def _analyse_option(self, option):
        if self.oracle is None:
            self.oracle = LiftingChecker._analyse_from_scratch(
                self, self._open_constants, option, set(), self.threshold
            )
        else:
            LiftingChecker._analyse_sub_options(self, self.oracle, option)

    def cegar_analyse_option(self, option):
        self.iterations += 1
        logger.info("CEGAR: iteration {}, analysing option {}.".format(self.iterations, option))
        self._analyse_option(option)

        threshold_synthesis_result = self.oracle.decided(self.threshold)
        if threshold_synthesis_result == ThresholdSynthesisResult.UNDECIDED:
            logger.debug("Undecided.")
            self.new_options = self.cegar_split_option(option)
        else:  # Decided option
            if (threshold_synthesis_result == ThresholdSynthesisResult.ABOVE) == self._accept_if_above[0]:
                logger.debug("All above or all below.")
                self.satisfying_assignment = option.pick_one_in_family()
            else:
                logger.debug("Decided: unsatisfying.")

    def run_feasibility(self):
        if self.input_has_optimality_property():
            return self._run_optimal_feasibility()
        if self.input_has_multiple_properties():
            raise RuntimeError("Lifting is only implemented for single properties")
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

# ------------------------------------------------------------------------------
# integrated method


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
            region_stat = [round(x, 3) for x in region_stat]
            storm_stat = [round(x, 3) for x in storm_stat]
            s += "> {} : {}\n".format(region_stat, storm_stat)
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
        self.property = None
        self.mdp = None
        self.mdp_mc_result = None
        self.allowed_to_split_options = True

    def initialise(self):
        CEGARChecker.initialise(self)
        CEGISChecker.initialise(self)
        assert len(self._verifier.properties) == 1
        self.property = self._verifier.properties[0].property

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
        self.mdp = self.oracle.mdp_handling().mdp()
        self.mdp_mc_result = self.oracle.latest_result().result

    def cegar_split_option(self, option):
        """Split option when allowed."""
        return super().cegar_split_option(option) if self.allowed_to_split_options else []

    def naive_stats(self, instance, all_conflicts=True):
        """Naive counterexample generation (for comparison)."""
        model = self.verifier().build_model(instance)
        qualitative_conflicts_properties, quantitative_conflict_properties = \
            self.verifier().naive_check_model(model, all_conflicts)

        if qualitative_conflicts_properties:
            # conflicts.add(tuple([c.name for c in self.sketch.used_constants()]))
            # TODO handling for qualitative conflicts can certainly be improved.
            return qualitative_conflicts_properties, set()

        # Construct the environment for the counterexample generator.
        env = stormpy.core.Environment()
        env.solver_environment.set_linear_equation_solver_type(stormpy.EquationSolverType.native)
        # env.solver_environment.set_force_sound()

        # We can sometimes merge properties into a single meta-property for conflict analysis.
        merged_conflict_props = self.verifier().merge_conflict_properties(quantitative_conflict_properties)
        assert(len(merged_conflict_props) == 1)
        (p, additional) = next(iter(merged_conflict_props.items()))

        # Create input for the counterexample generation.
        symbolic_model = stormpy.SymbolicModelDescription(instance)
        cex_input = stormpy.core.SMTCounterExampleGenerator.precompute(env, symbolic_model, model, p.raw_formula)
        for a in additional:
            cex_input.add_reward_and_threshold(a[0], a[1])

        # Prepare execution of the counterexample generation
        cex_stats = stormpy.core.SMTCounterExampleGeneratorStats()
        # Generate the counterexample
        result = stormpy.core.SMTCounterExampleGenerator.build(
            env, cex_stats, symbolic_model, model, cex_input,
            self._verifier().dont_care_set(), self._verifier().cex_options
        )
        assert(result.__len__() == 1)
        critical_edges_fs = result.pop()

        # Translate the counterexamples into conflicts.
        conflicting_holes = self._verifier().conflict_analysis(critical_edges_fs)

        return len(critical_edges_fs), len(conflicting_holes)

    def cegis_analyse_option(self, builder_options, option, mdp, mdp_result):
        """Analyse a region using provided mdp data to construct smaller counterexamples."""
        logger.info("CEGIS: analysing option {}.".format(option))
        self.statistic.bound = mdp_result.at(mdp.initial_states[0])

        # reset solver
        self.hole_options = option
        self._initialize_solver()

        # prepare counterexample generator
        counterexample = stormpy.SynthesisResearchCounterexample(
            IntegratedChecker.expanded_per_iter, self.property.raw_formula, mdp, mdp_result
        )

        while True:
            self.cegis_iterations += 1
            logger.info("CEGIS: iteration {}.".format(self.cegis_iterations))

            # get satisfiable assignment
            solver_result = self.solver.check()
            if solver_result != z3.sat:
                logger.debug("No further instances to explore.")
                break
            sat_model = self.solver.model()

            logger.debug("Iteration: {} instantiating..".format(self.stats.iterations))
            # Create an assignment for the holes ..
            hole_assignments = self._sat_model_to_constants_assignment(sat_model)
            # and construct instance ..
            instance = self.build_instance(hole_assignments)

            # construct and model check a DTMC
            dtmc = stormpy.build_sparse_model_with_options(instance, builder_options)
            assert len(dtmc.initial_states) == 1  # to avoid ambiguity
            assert dtmc.initial_states[0] == 0  # is implied by topological ordering
            logger.info("Built a DTMC with {} states.".format(dtmc.nr_states))

            dtmc_sat, dtmc_result = check_model(dtmc, self.property, quantitative=True)
            if dtmc_sat:
                self.satisfying_assignment = hole_assignments
                break

            # logger.debug("Constructing a minimal counterexample.")
            critical_edges = counterexample.construct(dtmc, dtmc_result)
            conflict = self._verifier().conflict_analysis(critical_edges)

            # add new clause
            clause = z3.Not(z3.And(
                [var == sat_model[var] for var, hole in self.template_meta_vars.items() if hole in conflict]
            ))
            self.solver.add(clause)

        self.statistic.end_region(counterexample.stats)

    def run_feasibility(self):
        """Run feasibility synthesis."""
        assert not self.input_has_optimality_property()
        assert not self.input_has_multiple_properties()
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
                logger.info("Storing hole option {} for CEGIS processing.".format(option))
                mdp_problems.append((option, self.mdp, self.mdp_mc_result))
        logger.info("MDP model checking finished after {} iterations, there are {} areas to explore.".format(
            self.cegar_iterations, len(mdp_problems)
        ))

        # precompute DTMC builder options
        builder_options = stormpy.BuilderOptions([self.property.raw_formula])
        builder_options.set_build_with_choice_origins(True)
        builder_options.set_build_state_valuations(True)
        builder_options.set_add_overlapping_guards_label()

        # initiate CEGIS for each hole_option
        logger.info("Initiating CEGIS phase.")

        for (option, mdp, mdp_mc_result) in mdp_problems:
            self.cegis_analyse_option(builder_options, option, mdp, mdp_mc_result)
            if self.satisfying_assignment is not None:
                break

        return self.compose_result([])

    def run(self):
        assignment = self.run_feasibility()
        self.statistic.finished(assignment, (self.cegar_iterations, self.cegis_iterations))


class Research:
    """Entry point: execution setup."""
    def __init__(
            self, check_prerequisites, backward_cuts,
            sketch_path, allowed_path, property_path, optimality_path, constants,
            restrictions, restriction_path
    ):

        assert not check_prerequisites
        assert not restrictions

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
            stats.append(self.run_algorithm(CEGISChecker))
            stats.append(self.run_algorithm(CEGARChecker))
            # stats.append(self.run_algorithm(IntegratedChecker))
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
