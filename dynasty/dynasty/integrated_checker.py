# author: Roman Andriushchenko
# co-author: Simon Stupinsky
import logging
import math
import time
import z3

import operator
import stormpy

from dynasty.family_checkers.cegis import Synthesiser
from dynasty.family_checkers.quotientbased import LiftingChecker
from dynasty.jani.jani_quotient_builder import JaniQuotientBuilder, ThresholdSynthesisResult

logger = logging.getLogger(__name__)


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


class Timer:
    def __init__(self):
        self.running = False
        self.timer = None
        self.time = 0

    def reset(self):
        self.__init__()

    def start(self):
        self.timer = self.timer if self.running else time.time()
        self.running = True

    def stop(self):
        self.time += time.time() - self.timer if self.running else 0
        self.timer = None if self.running else self.timer
        self.running = False

    def toggle(self):
        self.stop() if self.running else self.start()

    def read(self):
        return self.time + (time.time() - self.timer) if self.running else self.time


class Statistic:
    """General computation stats."""

    def __init__(self, method):
        self.method = method
        self.timer = Timer()
        self.assignment = {}
        self.iterations = 0
        self.optimal_value = None
        self.result = None
        self.timer.toggle()

    def finished(self, assignment, iterations, optimal_value):
        self.timer.toggle()
        self.result = assignment is not None
        self.assignment = {k: v.__str__() for (k, v) in assignment.items()} if assignment is not None else None
        self.iterations = iterations
        self.optimal_value = optimal_value

    def __str__(self):
        is_feasible = "feasible" if self.result or self.optimal_value else "unfeasible"
        return f"> {self.method}: " \
               f"{is_feasible} ({self.iterations} iters, {round(self.timer.time, 2)} sec, opt: {self.optimal_value})\n"


class CEGISChecker(Synthesiser):
    """CEGIS wrapper."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.statistic = Statistic("CEGIS")

    def run(self):
        _, assignment, opt_value, iters = self.run_feasibility()
        self.statistic.finished(assignment, iters, opt_value)


class CEGARChecker(LiftingChecker):
    """CEGAR wrapper."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.statistic = Statistic("CEGAR")
        self.iterations = 0
        self.optimal_iterations = 0
        self.optimal_value = None
        self.use_oracle = True
        self.new_options = None
        self.satisfying_assignment = None
        self.oracle = None
        self.optimal_option = None

    def cegar_initialisation(self):
        self.optimal_value = (0.0 if self._optimality_setting.direction == "max" else math.inf) if self._optimality_setting is not None else None
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes
        return [(
            self.hole_options,
            [True] * len(self.mc_formulae) + ([False] if self._optimality_setting is not None else [])
        )]

    def cegar_split_option(self, option, index=0):
        self.oracle.scheduler_color_analysis(index)
        return self._split_hole_options(option, self.oracle)

    def __analyse_from_scratch(self, option):
        self.oracle = LiftingChecker._analyse_from_scratch(self, self._open_constants, option, set())

    def __analyse_suboptions(self, option):
        LiftingChecker._analyse_sub_options(self, self.oracle, option)

    def _analyse_option(self, option):
        if self.oracle is None:
            self.__analyse_from_scratch(option)
        else:
            self.__analyse_suboptions(option)

    def cegar_analyse_option(self, hole_options_map, last=False):
        option, undecided_formulae = hole_options_map.pop(-1 if last else 0)
        self.iterations += 1
        is_max = self._optimality_setting.direction == "max" if self.input_has_optimality_property() else None

        self.copy_formulae_attrs()
        self.oracle = self._delete_sat_formulae([idx for idx, uf in enumerate(undecided_formulae) if uf], self.oracle)
        undecided_indices = list(range(0, len(self.mc_formulae)))

        logger.info(f"CEGAR: iteration {self.iterations}, analysing option {option}.")
        self._analyse_option(option)

        threshold_synthesis_results = self.oracle.decided(self.thresholds)

        if self._contains_unsat_result(threshold_synthesis_results):
            logger.debug("Unsatisfying.")
        else:
            undecided_indices = \
                [idx for idx, r in enumerate(threshold_synthesis_results) if r == ThresholdSynthesisResult.UNDECIDED]
            if undecided_indices:
                logger.debug("Undecided.")
                self.new_options = self.cegar_split_option(option)
            else:
                if self.input_has_optimality_property():
                    sat, candidate_option, value, iters, latest_result, self.new_options = \
                        self._run_optimal_feasibility(option, one_iter=True)
                    if (is_max and value > self.optimal_value) or (not is_max and value < self.optimal_value):
                        self.optimal_value = value
                        self.optimal_option = candidate_option
                        self.optimal_iterations = iters

                        hole_options_map = self._violation_property_update(
                            self.optimal_value, self.oracle, hole_options_map
                        )
                        undecided_indices.append(len(undecided_formulae) - 1)
                        self.oracle.latest_results.append(latest_result)
                else:
                    logger.debug("Satisfying.")
                    self.satisfying_assignment = option.pick_one_in_family()

        return self._get_undecided_formulae(undecided_formulae, undecided_indices), hole_options_map

    def perform_iteration(self, hole_options_map):
        undecided_formulae, hole_options_map = self.cegar_analyse_option(hole_options_map)
        if self.new_options is not None:
            self.new_options = [(new_option, undecided_formulae[:]) for new_option in self.new_options]
            hole_options_map = self.new_options + hole_options_map
            self.new_options = None
        return hole_options_map

    def run_feasibility(self):
        if self.input_has_restrictions():
            raise RuntimeError("Restrictions are not supported by quotient based approaches")

        hole_options_map = self.cegar_initialisation()

        while len(hole_options_map) > 0:
            hole_options_map = self.perform_iteration(hole_options_map)
            if self.satisfying_assignment is not None:
                return self.satisfying_assignment

        if self.input_has_optimality_property():
            self.iterations += self.optimal_iterations
            return self.optimal_option

        logger.info("No more options to explore.")
        return None

    def run(self):
        assignment = self.run_feasibility()
        self.statistic.finished(assignment, self.iterations, self.optimal_value)


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

    def __init__(self):
        CEGISChecker.__init__(self)
        CEGARChecker.__init__(self)
        self.cegis_iterations = 0
        self.cegar_iterations = 0
        self.statistic = IntegratedStatistic()
        self.mdp = None
        self.mdp_mc_results = []
        self.allowed_to_split_options = True
        self.hole_option_indices = None
        self.models_total = 0
        self.stage_timer = Timer()
        self.stage_switch_allowed = True  # once a method wins, set this to false and do not switch between methods
        self.stage_score = 0  # +1 point whenever cegar wins the stage, -1 otherwise
        # cegar/cegis stats
        self.stage_time_cegar, self.stage_pruned_cegar, self.stage_time_cegis, self.stage_pruned_cegis = 0, 0, 0, 0
        # multiplier to derive time allocated for cegis; =1 is fair, <1 favours cegar, >1 favours cegis
        self.cegis_allocated_time_factor = 1.0
        # start with CEGAR
        self.stage_cegar = True
        self.cegis_allocated_time = 0
        self.stage_time_allocation_cegis = 0
        # CE quality
        self.ce_maxsat, self.ce_zero, self.ce_global, self.ce_local, self.ce_holes, self.ce_states = 0, 0, 0, 0, 0, 0
        self.ce_maxsat_timer, self.ce_zero_timer, self.ce_global_timer, self.ce_local_timer = \
            Timer(), Timer(), Timer(), Timer()
        self.global_mdp = None
        self.global_mdp_results = []
        self.counterexamples_global = []
        self.ce_quality_compute = False

    def stage_start(self, request_stage_cegar):
        self.stage_cegar = request_stage_cegar
        self.stage_timer.reset()
        self.stage_timer.start()

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
        elif self.optimal_option is not None:
            self.cegar_iterations += self.optimal_iterations
            return self.optimal_option
        elif len(hole_options) == 0:
            logger.info("No more options.")
            return None

    def cegar_analyse_option(self, problems, last=True):
        """Analyse region and store mdp data."""
        hole_options_map = [(option, formulae[:]) for (option, formulae, _, _) in problems]
        undecided_formulae, hole_options_map = CEGARChecker.cegar_analyse_option(self, hole_options_map, last=True)
        problems = [(o, f, b, s) for (o, f), (_, _, b, s) in zip(hole_options_map, problems[:-1])]
        self.cegar_iterations += 1
        self.mdp = self.oracle.mdp_handling.mdp
        self.mdp_mc_results = [self.oracle.latest_results.pop(0).result for f in undecided_formulae if f]
        return undecided_formulae, problems

    def stage_step(self, models_pruned):
        """Performs a stage step, returns True if the method switch took place"""

        # if the method switch is prohibited, we do not care about stats
        if not self.stage_switch_allowed:
            return False

        # record pruned models
        self.stage_pruned_cegar += models_pruned / self.models_total if self.stage_cegar else 0
        self.stage_pruned_cegis += models_pruned / self.models_total if not self.stage_cegar else 0

        # allow cegis another stage step if some time remains
        if not self.stage_cegar and self.stage_timer.read() < self.cegis_allocated_time:
            return False

        # stage is finished: record time
        self.stage_timer.stop()
        current_time = self.stage_timer.read()
        if self.stage_cegar:
            # cegar stage over: allocate time for cegis and switch
            self.stage_time_cegar += current_time
            self.cegis_allocated_time = current_time * self.cegis_allocated_time_factor
            self.stage_start(request_stage_cegar=False)
            return True

        # cegis stage over
        self.stage_time_cegis += current_time

        # calculate average success rate, update stage score
        success_rate_cegar = self.stage_pruned_cegar / self.stage_time_cegar
        success_rate_cegis = self.stage_pruned_cegis / self.stage_time_cegis
        if success_rate_cegar > success_rate_cegis:
            # cegar wins the stage
            self.stage_score += 1
            if self.stage_score >= self.stage_score_limit:
                # cegar wins the synthesis
                # print("> only cegar")
                self.stage_switch_allowed = False
                # switch back to cegar
                self.stage_start(request_stage_cegar=True)
                return True
        elif success_rate_cegar < success_rate_cegis:
            # cegis wins the stage
            self.stage_score -= 1
            if self.stage_score <= -self.stage_score_limit:
                # cegar wins the synthesis
                # print("> only cegis")
                self.stage_switch_allowed = False
                # no need to switch
                return False

        # neither method prevails: adjust cegis time allocation factor
        if self.stage_pruned_cegar == 0 or self.stage_pruned_cegis == 0:
            cegar_dominance = 1
        else:
            cegar_dominance = success_rate_cegar / success_rate_cegis
        cegis_dominance = 1 / cegar_dominance
        self.stage_time_allocation_cegis = cegis_dominance

        # stage log
        print(
            f"> {success_rate_cegar:.2f} \\\\ {success_rate_cegis:.2f} = {cegis_dominance:.1f} ({self.stage_score})"
        )

        # switch back to cegar
        self.stage_start(request_stage_cegar=True)
        return True

    def relevant_holes(self, critical_edges, relevant_holes):
        holes = self.verifier.conflict_analysis(critical_edges)
        holes = [hole for hole in holes if hole in relevant_holes]
        return holes

    # ----- CE quality ----- #

    def ce_quality_global(self, mdp, mdp_results):
        if not(not self.ce_quality_compute or self.global_mdp is not None):
            self.global_mdp = mdp
            self.global_mdp_results = mdp_results[:]

    def ce_quality_measure(self, instance, relevant_holes, counterexample, dtmc, idx):
        if not self.ce_quality_compute:
            return
        self.statistic.timer.stop()
        self.stage_timer.stop()

        # maxsat
        self.ce_maxsat_timer.start()
        _, conflict_maxsat = self.verifier.naive_check(instance, all_conflicts=True, check_conflicts=False)
        conflict_maxsat = [hole for hole in conflict_maxsat if hole in relevant_holes]
        self.ce_maxsat += len(conflict_maxsat) / len(relevant_holes)
        self.ce_maxsat_timer.stop()

        # zero
        self.ce_zero_timer.start()
        conflict_zero = counterexample.construct_via_holes(dtmc, False)
        self.ce_zero += len(conflict_zero) / len(relevant_holes)
        self.ce_zero_timer.stop()

        # global
        self.ce_global_timer.start()
        conflict_global = self.counterexamples_global[idx].construct_via_holes(dtmc, True)
        self.ce_global += len(conflict_global) / len(relevant_holes)
        self.ce_global_timer.stop()

        # resume timers and compute normal bounds
        self.stage_timer.start()
        self.statistic.timer.start()

        # local
        self.ce_local_timer.start()
        conflict_local = counterexample.construct_via_holes(dtmc, True)
        self.ce_local += len(conflict_local) / len(relevant_holes)
        self.ce_local_timer.stop()

        print(f"> {self.ce_maxsat / self.cegis_iterations} vs {self.ce_local / self.cegis_iterations}")


    def ce_quality_print(self):
        if not self.ce_quality_compute:
            return
        if self.cegis_iterations < 2:
            print("> ce quality: n/a")
        else:
            print(
                f"> ce quality: {self.ce_maxsat / self.cegis_iterations:1.4f} - "
                f"{self.ce_zero / self.cegis_iterations:1.4fs} - {self.ce_global / self.cegis_iterations:1.4f} - "
                f"{self.ce_holes / self.cegis_iterations:1.4f}"
            )
            print(f"> ce time: "
                  f"{self.ce_maxsat_timer.read() / self.cegis_iterations:1.4f} - "
                  f"{self.ce_zero_timer.read() / self.cegis_iterations:1.4f} - "
                  f"{self.ce_global_timer.read() / self.cegis_iterations:1.4f} - "
                  f"{self.ce_local_timer.read() / self.cegis_iterations:1.4f}"
            )

    # ----- CE quality ----- #

    def _construct_violation_cex(self, family, relevant_holes_flatset):
        vp = self._construct_violation_property(self.optimal_value)
        self._set_optimality_setting()
        analyse_result = self._analyse_from_scratch(self._open_constants, family, set())
        mdp_result = analyse_result.latest_results[0].result
        CEGARChecker.initialise(self)

        return stormpy.SynthesisResearchCounterexample(
            self.sketch, relevant_holes_flatset, vp.raw_formula, analyse_result.mdp_handling.mdp, mdp_result
        )

    def _update_problems(self, problems, problem):
        hole_options_map = [(o, f) for (o, f, _, _) in problems]
        hole_options_map = self._violation_property_update(
            self.optimal_value, self.oracle, hole_options_map
        )
        assert len(hole_options_map) == len(problems)
        problems = [(o, f, b, s) for (o, f), (_, _, b, s) in zip(hole_options_map, problems)]
        problem[1][-1] = True
        return problems, problem

    def _prepare_properties(self, mdp_results, formulae):
        assert len(self._properties) == len(formulae)
        self.properties = [self._properties[idx] for idx, uf in enumerate(formulae) if uf]
        # mdp_result was not generated for violation property, therefore we will ignore it
        self.properties = self.properties[:-1] if len(mdp_results) + 1 == len(self.properties) else self.properties
        assert len(mdp_results) == len(self.properties)

    def _construct_cex_for_index(self, counterexamples, dtmc, family_clauses, sat_model, index):
        conflict = counterexamples[index].construct_via_holes(dtmc, True)
        # add new clause
        cex_clauses = family_clauses.copy()
        for var, hole in self.template_meta_vars.items():
            if hole in conflict:
                cex_clauses[hole] = (var == sat_model[var])
        counterexample_encoding = z3.Not(z3.And(list(cex_clauses.values())))
        self.solver.add(counterexample_encoding)

    def cegis_analyse_family(self, builder_options, problems):
        """Analyse a family using provided mdp data to construct generalized counterexamples."""
        logger.debug("CEGIS stage.")

        problem = problems.pop(-1)
        family, formulae, (mdp, mdp_results), _ = problem
        self._prepare_properties(mdp_results, formulae)

        if self.only_cegis:
            # disallow return to CEGAR
            self.stage_switch_allowed = False

        # list of relevant holes (open constants) in this subfamily
        relevant_holes = [hole for hole in self.holes if len(family[hole]) > 1]

        # encode family
        family_clauses = dict()
        for var, hole in self.template_meta_vars.items():
            family_clauses[hole] = z3.Or([var == self.hole_option_indices[hole][option] for option in family[hole]])
        family_encoding = z3.And(list(family_clauses.values()))

        # Prepare counter-example generator for each given property
        relevant_holes_flatset = stormpy.core.FlatSetString()
        [relevant_holes_flatset.insert(hole) for hole in relevant_holes]
        counterexamples = []
        for idx, (prop, mdp_result) in enumerate(zip(self.get_properties(), mdp_results)):
            counterexamples.append(stormpy.SynthesisResearchCounterexample(
                self.sketch, relevant_holes_flatset, prop.raw_formula, mdp, mdp_result
            ))
            # CE generator for global MDP bounds
            if self.ce_quality_compute:
                self.counterexamples_global.append(stormpy.SynthesisResearchCounterexample(
                    self.sketch, relevant_holes_flatset, prop.raw_formula, self.global_mdp, self.global_mdp_results[idx]
                ))
        if self._optimality_setting is not None:
            counterexamples.append(None)

        # get satisfiable assignments (withing the subfamily)
        solver_result = self.solver.check(family_encoding)
        while solver_result == z3.sat:
            self.cegis_iterations += 1
            logger.info("CEGIS iteration {}.".format(self.cegis_iterations))

            # Get satisfiable assignment
            sat_model = self.solver.model()
            # Create an assignment for the holes ..
            hole_assignments = self._sat_model_to_constants_assignment(sat_model)
            # and construct instance ..
            instance = self.build_instance(hole_assignments)

            # construct and model check a DTMC
            dtmc = stormpy.build_sparse_model_with_options(instance, builder_options)
            # assert that none of the states contains deadlock (easier notation?)
            assert dtmc.labeling.get_states("deadlock").number_of_set_bits() == 0

            logger.debug("Constructed DTMC of size {}.".format(dtmc.nr_states))

            # cols = []
            # vals = []
            # r_size = []
            # for i in range(0, dtmc.transition_matrix.nr_rows):
            #     cnt = 0
            #     row = dtmc.transition_matrix.get_row(i)
            #     for r in row:
            #         cnt += 1
            #         cols.append(r.column)
            #         vals.append(r.value())
            #     r_size.append(cnt)
            # print(f">>> {cols}")
            # print(f">>> {vals}")
            # print(f">>> {r_size}")
            # print(f">>> {len(vals)}")
            # exit(1)

            assert len(dtmc.initial_states) == 1  # to avoid ambiguity
            assert dtmc.initial_states[0] == 0  # should be implied by topological ordering

            satisfied = []
            for index, prop in enumerate(self.get_properties()):
                dtmc_sat, dtmc_result = check_model(dtmc, prop, quantitative=True)
                satisfied.append(dtmc_sat)
                if not dtmc_sat:
                    self._construct_cex_for_index(counterexamples, dtmc, family_clauses, sat_model, index)

                    # estimate number of (virtually) pruned models
                    # models_pruned = 1
                    # irrelevant_holes = set(relevant_holes) - set(conflict)
                    # for hole in irrelevant_holes:
                    #     models_pruned *= len(family[hole])

                    # compare to maxsat, state exploration, naive hole exploration, global vs local bounds
                    # self.ce_quality_measure(
                    #     instance, relevant_holes, counterexamples[index], dtmc, index
                    # )

            if all(satisfied):  # SAT
                if self.input_has_optimality_property():
                    dtmc_result = stormpy.model_checking(dtmc, self._optimality_setting.criterion)
                    if self._optimality_setting.is_improvement(
                            dtmc_result.at(dtmc.initial_states[0]), self.optimal_value
                    ):
                        logger.debug("Optimal value improved to {}.".format(dtmc_result.at(dtmc.initial_states[0])))
                        self.optimal_value = dtmc_result.at(dtmc.initial_states[0])
                        self.optimal_option = hole_assignments
                        problems, problem = self._update_problems(problems, problem)
                        counterexamples[len(counterexamples) - 1] = \
                            self._construct_violation_cex(family, relevant_holes_flatset)
                    else:
                        logger.debug("Optimal value ({}) not improved, conflict analysis!".format(self.optimal_value))
                        counterexamples[len(counterexamples) - 1] = \
                            self._construct_violation_cex(family, relevant_holes_flatset)
                        self._construct_cex_for_index(
                            counterexamples, dtmc, family_clauses, sat_model, len(counterexamples) - 1
                        )
                else:
                    self.satisfying_assignment = hole_assignments
                    break

            # read next solution
            solver_result = self.solver.check(family_encoding)

            # record stage
            if self.stage_step(0):
                # switch requested
                assert self.stage_cegar
                return False, problems, problem

        # full subfamily pruned
        assert self.solver.check(family_encoding) == z3.unsat or self.satisfying_assignment
        return True, problems, problem

    def _construct_hole_option_indices(self):
        self.hole_option_indices = dict()
        for hole, options in self.hole_options.items():
            indices = dict()
            k = 0
            for option in options:
                indices[option] = k
                k += 1
            self.hole_option_indices[hole] = indices

    def run_feasibility(self):
        """Run feasibility synthesis."""
        logger.info("Running feasibility synthesis.")

        # precompute DTMC builder options
        raw_formulae = [p.property.raw_formula for p in self.get_properties()]
        if self.input_has_optimality_property():
            raw_formulae.append(self._optimality_setting.criterion.raw_formula)
        builder_options = stormpy.BuilderOptions(raw_formulae)
        builder_options.set_build_with_choice_origins(True)
        builder_options.set_build_state_valuations(True)
        builder_options.set_add_overlapping_guards_label()

        # initialize solver describing the family and counterexamples
        # note: restricting to subfamilies is encoded separately
        self._initialize_solver()
        # a map for indices of options
        self._construct_hole_option_indices()

        # initialize cegar
        families = self.cegar_initialisation()
        # identify edges with open constants
        family, formulae = families[0]
        logger.info("Family members: {}.".format(family.size()))

        # initiate cegar-cegis loop
        problems = [(family, formulae, None, None)]
        self.models_total = family.size()
        self.stage_start(request_stage_cegar=True)

        while problems:
            logger.debug("Current number of problems: {}".format(len(problems)))
            # pick a family
            problem = problems[-1]
            family, formulae, bound, subfamilies = problem
            family_size = family.size()
            logger.info("Analysing subfamily of size {}.".format(family_size))

            if self.stage_cegar:  # CEGAR
                if subfamilies is not None:
                    # family has been already analysed: refine and continue
                    # note: subfamilies inherit bound and formulae from the parent family
                    problems.pop(-1)
                    logger.info("Splitting the family.")
                    sub_problems = [(subfamily, formulae, bound, None) for subfamily in subfamilies]
                    problems.extend(sub_problems)
                    continue

                # family has not been analysed yet
                logger.info("CEGAR iteration {}.".format(self.cegar_iterations+1))
                undecided_formulae, problems = self.cegar_analyse_option(problems)
                bound = (self.mdp, self.mdp_mc_results)
                if self.satisfying_assignment is not None:
                    logger.debug("Sat")
                    break
                if self.new_options is None:
                    logger.debug("Unsat")
                    models_pruned = family_size
                else:
                    logger.debug("Undecided.")
                    models_pruned = 0
                    # assert (len(self.new_options) == 2)
                    # the cegar family was splitted
                    if len(self.new_options) == 2:
                        problems.append((family, undecided_formulae[:], bound, self.new_options[:]))  # DFS
                    # problems = [(family, undecided_formulae[:], bound, self.new_options)] + problems  # BFS
                    self.new_options = None
                    if self.ce_quality_compute:
                        self.ce_quality_global(self.mdp, self.mdp_mc_results)
                self.stage_step(models_pruned)

            else:  # CEGIS
                assert bound is not None
                analysis_success, problems, problem = self.cegis_analyse_family(builder_options, problems)
                if self.satisfying_assignment is not None:  # sat
                    logger.debug("Sat")
                    break
                if analysis_success:
                    logger.debug("CEGIS Unsat")
                    self.stage_step(family_size)
                else:  # stage unsuccessful: leave the family to cegar; note: phase switched implicitly
                    logger.debug("Stage interrupted.")
                    problems.append(problem)

        assert len(problems) == 0 or self.satisfying_assignment
        return self.compose_result([])

    def run(self):
        assignment = self.run_feasibility()
        self.statistic.finished(assignment, (self.cegar_iterations, self.cegis_iterations), self.optimal_value)
        self.ce_quality_print()


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

        # import research.generator1
        # import research.generator2
        # workspace.generator2.run()

        workdir = "workspace/experiments"
        with open(f"{workdir}/parameters.txt", 'r') as f:
            lines = f.readlines()
            regime = int(lines[0])
            stage_score_limit = int(lines[1])
        IntegratedChecker.stage_score_limit = stage_score_limit

        stats = []

        if regime == 0:
            # stats.append(self.run_algorithm(CEGISChecker))
            # stats.append(self.run_algorithm(CEGARChecker))
            stats.append(self.run_algorithm(IntegratedChecker))
        elif regime == 1:
            stats.append(self.run_algorithm(CEGISChecker))
        elif regime == 2:
            stats.append(self.run_algorithm(CEGARChecker))
        elif regime == 3:
            stats.append(self.run_algorithm(IntegratedChecker))
        # elif regime in [2,3]:
        # stats.append(self.run_algorithm(IntegratedChecker))
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
