import itertools
import logging
import math
import time

from collections import OrderedDict
from collections.abc import Iterable

import dynasty.jani
import stormpy.core

from dynasty.annotated_property import AnnotatedProperty
from dynasty.jani.jani_quotient_builder import JaniQuotientBuilder, ModelHandling
from dynasty.jani.quotient_container import ThresholdSynthesisResult as ThresholdSynthesisResult
from dynasty.family_checkers.familychecker import FamilyChecker, HoleOptions

logger = logging.getLogger(__name__)


class QuotientBasedFamilyChecker(FamilyChecker):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.mc_formulae, self._mc_formulae = None, None
        self.mc_formulae_alt, self._mc_formulae_alt = None, None
        self.jani_quotient_builder = None
        self.thresholds, self._thresholds = None, None
        self._accept_if_above, self.__accept_if_above = None, None

    def initialise(self):
        self._mc_formulae = []
        self._mc_formulae_alt = []
        self._thresholds = []
        self.__accept_if_above = []

        for p in self.get_all_properties():
            formula = p.raw_formula.clone()
            self._thresholds.append(formula.threshold)
            formula.remove_bound()
            alt_formula = formula.clone()
            if formula.comparison_type in [stormpy.ComparisonType.LESS, stormpy.ComparisonType.LEQ]:
                formula.set_optimality_type(stormpy.OptimizationDirection.Minimize)
                alt_formula.set_optimality_type(stormpy.OptimizationDirection.Maximize)
                accept_if_above = False
            else:
                assert formula.comparison_type in [stormpy.ComparisonType.GREATER, stormpy.ComparisonType.GEQ]
                formula.set_optimality_type(stormpy.OptimizationDirection.Maximize)
                alt_formula.set_optimality_type(stormpy.OptimizationDirection.Minimize)
                accept_if_above = True

            self._mc_formulae.append(formula)
            self._mc_formulae_alt.append(alt_formula)
            self.__accept_if_above.append(accept_if_above)
        self.copy_formulae_attrs()

    def copy_formulae_attrs(self):
        self.mc_formulae = self._mc_formulae[:]
        self.mc_formulae_alt = self._mc_formulae_alt[:]
        self.thresholds = self._thresholds[:]
        self._accept_if_above = self.__accept_if_above[:]

    def _set_optimality_setting(self):
        if self._optimality_setting is not None:
            opt_formula = self._optimality_setting.criterion.raw_formula.clone()
            opt_alt_formula = self._optimality_setting.criterion.raw_formula.clone()
            if self._optimality_setting.direction == "max":
                opt_formula.set_optimality_type(stormpy.OptimizationDirection.Maximize)
                opt_alt_formula.set_optimality_type(stormpy.OptimizationDirection.Minimize)
            else:
                assert self._optimality_setting.direction == "min"
                opt_formula.set_optimality_type(stormpy.OptimizationDirection.Minimize)
                opt_alt_formula.set_optimality_type(stormpy.OptimizationDirection.Maximize)
            self.mc_formulae = [opt_formula]
            self.mc_formulae_alt = [opt_alt_formula]
            self.thresholds = [math.inf if self._optimality_setting.direction == "min" else 0.0]
            self._accept_if_above = [self._optimality_setting.direction == "max"]

    def _analyse_from_scratch(self, _open_constants, holes_options, all_in_one_constants):
        remember = set()  # set(_open_constants)#set()
        jani_abstraction_result = self.jani_quotient_builder.construct(holes_options, remember, all_in_one_constants)
        jani_abstraction_result.prepare(self.mc_formulae, self.mc_formulae_alt, self._engine)
        for index, threshold in enumerate(self.thresholds):
            logger.info("Run analysis of property with index {}".format(index))
            jani_abstraction_result.analyse(threshold, index, self._engine)
        return jani_abstraction_result

    def _analyse_sub_options(self, oracle, sub_options):
        indexed_sub_options = self.hole_options.index_map(sub_options)
        oracle.consider_subset(sub_options, indexed_sub_options)
        oracle._latest_results = []
        [oracle.analyse(threshold, index) for index, threshold in enumerate(self.thresholds)]
        return oracle

    def _check_next_round(self, oracle, hole_options, hole_options_next_round, nr_options_remaining):
        logger.info(f"Number options remaining: {nr_options_remaining}")
        logger.info(f"Singleton regions {oracle.dtmcs_checked}")
        logger.info(
            f"Critical timings so far: {oracle.build_time} building, "
            f"{oracle.mc_time} checking {oracle.sched_ana_time} analysis."
        )

        ret_val = None
        if len(hole_options) == 0:
            ret_val = True if len(hole_options_next_round) == 0 else False
            logger.info("Next round...")
            if len(hole_options_next_round) * 8 > nr_options_remaining:
                self.use_oracle = False
        return ret_val


class LiftingChecker(QuotientBasedFamilyChecker):
    """
    The lifting technique described in the TACAS 2019 paper: Shepherding of hordes of Markov Chains.

    TODO use different splitting heuristics for different tasks
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.use_oracle = True
        self._open_constants = OrderedDict()

    def _contains_unsat_result(self, results):
        for index, result in enumerate(results):
            if (result == ThresholdSynthesisResult.ABOVE) and (not self._accept_if_above[index]) or \
                    (result == ThresholdSynthesisResult.BELOW) and self._accept_if_above[index]:
                return True
        return False

    def _delete_sat_formulae(self, undecided, oracle):
        self.mc_formulae = [f for i, f in enumerate(self.mc_formulae) if i in undecided]
        self.mc_formulae_alt = [f for i, f in enumerate(self.mc_formulae_alt) if i in undecided]
        self.thresholds = [t for i, t in enumerate(self.thresholds) if i in undecided]
        self._accept_if_above = [t for i, t in enumerate(self._accept_if_above) if i in undecided]
        if oracle is not None:
            oracle.mdp_handling._formulae = self.mc_formulae[:]
            oracle.mdp_handling._alt_formulae = self.mc_formulae_alt[:]
        assert len(self.mc_formulae) == len(self.mc_formulae_alt) == len(self.thresholds) == \
               len(self._accept_if_above) == len(undecided)
        return oracle

    def _construct_violation_property(self, optimal_value):
        return self._optimality_setting.get_violation_property(
            optimal_value,
            lambda x: self.sketch.expression_manager.create_rational(stormpy.Rational(x)),
        )

    def _add_violation_property(self, violation_property):
        self._properties[len(self._properties) - 1] = violation_property
        if self.properties:
            self.properties[len(self.properties) - 1] = violation_property
        else:
            self.properties.append(violation_property)

    def _violation_property_update(self, optimal_value, oracle, hole_options_map):
        vp = self._construct_violation_property(optimal_value)
        self._add_violation_property(AnnotatedProperty(vp, self.sketch, False))
        self.initialise()
        oracle.prepare(self.mc_formulae, self.mc_formulae_alt, self._engine)
        hole_options_map = [(o, f[:-1] + [True]) for (o, f) in hole_options_map]
        return hole_options_map

    @staticmethod
    def _get_undecided_formulae(undecided_formulae, undecided_indices):
        checked_formula = 0
        for idx, formula in enumerate(undecided_formulae):
            if formula:
                undecided_formulae[idx] = checked_formula in undecided_indices
                checked_formula += 1
        return undecided_formulae

    @staticmethod
    def _get_new_options(nr_options_remaining, hole_options):
        return nr_options_remaining - hole_options[0].size(), hole_options[1:]

    @staticmethod
    def _get_new_options_map(nr_options_remaining, hole_options_map):
        return nr_options_remaining - hole_options_map[0][0].size(), hole_options_map[1:]

    def run_feasibility(self):
        if self.input_has_restrictions():
            raise RuntimeError("Restrictions are not supported by quotient based approaches")

        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes

        oracle, optimal_hole_option = None, None
        iterations, optimal_iterations = 0, 0
        optimal_value = 0.0 if self._optimality_setting.direction == "max" else 99999
        hole_options_next_round = []
        sat = False

        hole_options_map = [(self.hole_options, [True] * len(self.mc_formulae))]
        nr_options_remaining = self.hole_options.size()
        logger.info(f"Total number of options: {self.hole_options.size()}")

        while True and nr_options_remaining:
            _, undecided_formulae = hole_options_map[0]
            self.copy_formulae_attrs()
            oracle = self._delete_sat_formulae([idx for idx, uf in enumerate(undecided_formulae) if uf], oracle)

            hole_options = [o for o, _ in hole_options_map]
            iterations, oracle, threshold_synthesis_results = self._perform_analysis(
                iterations, hole_options, hole_options_next_round, oracle,
            )

            if self._contains_unsat_result(threshold_synthesis_results):
                logger.debug("Unsatisfying.")
                nr_options_remaining, hole_options_map = \
                    self._get_new_options_map(nr_options_remaining, hole_options_map)
            else:
                undecided_indices = [
                    idx for idx, r in enumerate(threshold_synthesis_results) if r == ThresholdSynthesisResult.UNDECIDED
                ]
                if undecided_indices:
                    logger.debug("Undecided.")
                    oracle.scheduler_color_analysis()
                    new_options = self._split_hole_options(hole_options[0], oracle)
                    # undecided_formulae = self._get_undecided_formulae(undecided_formulae, undecided_indices)
                    undecided_formulae = undecided_formulae
                    new_options = [(new_option, undecided_formulae) for new_option in new_options]
                    hole_options_map = new_options[:] + hole_options_map[1:]
                else:
                    logger.debug("Satisfying.")
                    if self.input_has_optimality_property():
                        sat, hole_option, value, iters, _, _ = self._run_optimal_feasibility(hole_options[0])
                        if (self._optimality_setting.direction == "max" and value > optimal_value) or \
                                (self._optimality_setting.direction == "min" and value < optimal_value):
                            optimal_value = value
                            optimal_hole_option = hole_option
                            optimal_iterations = iters
                        nr_options_remaining, hole_options_map = \
                            self._get_new_options_map(nr_options_remaining, hole_options_map)
                        hole_options_map = self._violation_property_update(optimal_value, oracle, hole_options_map)
                        print("Hello world")
                        exit(1)
                    else:
                        return True, hole_options[0].pick_one_in_family(), None, iterations

                next_round = self._check_next_round(oracle, hole_options, hole_options_next_round, nr_options_remaining)
                if bool(next_round):
                    break
                elif next_round is not None:
                    hole_options_map, hole_options_next_round = hole_options_next_round, []

        return (sat, optimal_hole_option, optimal_value, optimal_iterations + iterations) \
            if self.input_has_optimality_property() else (False, None, None, iterations)

    def _run_optimal_feasibility(self, hole_option, one_iter=False):
        """

        :return:
        """
        oracle, optimal_hole_option = None, None
        iterations = 0

        hole_options = [hole_option]
        hole_options_next_round = []
        nr_options_remaining = self.hole_options.size()
        logger.info(f"Total number of options: {nr_options_remaining}")
        self._set_optimality_setting()
        is_max = self._optimality_setting.direction == "max"
        improved = False

        while True:
            iterations, oracle, threshold_synthesis_results = self._perform_analysis(
                iterations, hole_options, hole_options_next_round, oracle
            )

            if threshold_synthesis_results[0] == ThresholdSynthesisResult.UNDECIDED:
                logger.debug("Undecided.")
                improved = False
                if hole_options[0].size() > 1:
                    oracle.scheduler_color_analysis()
                    if (oracle.is_lower_bound_tight() and not is_max) or (oracle.is_upper_bound_tight() and is_max):
                        logger.debug(f'Found a tight {"upper" if is_max else "lower"} bound.')
                        self.thresholds[0] = oracle.upper_bound() if is_max else oracle.lower_bound()
                        logger.info(f"current threshold {self.thresholds[0]}")
                        improved = True

                    if improved:
                        nr_options_remaining -= 1 if optimal_hole_option is not None else 0
                        optimal_hole_option = hole_options[0]
                        nr_options_remaining, hole_options = self._get_new_options(nr_options_remaining, hole_options)
                    else:
                        hole_options = self._split_hole_options(hole_options[0], oracle) + hole_options[1:]
                else:
                    hole_options = hole_options[1:]

            else:
                improved_tight = None
                if (threshold_synthesis_results[0] == ThresholdSynthesisResult.ABOVE and is_max) or \
                        (threshold_synthesis_results[0] == ThresholdSynthesisResult.BELOW and not is_max):
                    logger.debug(f'All {"above" if is_max else "below"}.')
                    oracle.scheduler_color_analysis()
                    improved_tight = oracle.is_upper_bound_tight() if is_max else oracle.is_lower_bound_tight()
                    self.thresholds[0] = oracle.upper_bound() if \
                        (improved_tight and is_max) or (not improved_tight and not is_max) else oracle.lower_bound()
                    logger.info(f"current threshold {self.thresholds[0]}")
                else:
                    logger.debug("All discarded.")
                    nr_options_remaining, hole_options = self._get_new_options(nr_options_remaining, hole_options)

                if improved_tight:
                    optimal_hole_option = hole_options[0]
                    nr_options_remaining, hole_options = self._get_new_options(nr_options_remaining, hole_options)
                elif improved_tight is not None:
                    optimal_hole_option = None
                    hole_options = self._split_hole_options(hole_options[0], oracle) + hole_options[1:]

            next_round = self._check_next_round(oracle, hole_options, hole_options_next_round, nr_options_remaining)
            if bool(next_round) or one_iter:
                break
            elif next_round is not None:
                hole_options, hole_options_next_round = hole_options_next_round, []

            logger.info(f"Optimal value at {self.thresholds[0]} with {optimal_hole_option}")

        # TODO: which member of the family has optimal solution
        hole_options = hole_options_next_round if next_round is not None else hole_options
        assert len(oracle.latest_results) == 1
        return improved, optimal_hole_option.pick_one_in_family() if optimal_hole_option is not None else None, \
            self.thresholds[0], iterations, oracle.latest_results[0], hole_options

    def _perform_analysis(self, iterations, hole_options, hole_options_next_round, oracle):
        iterations += 1
        logger.info(
            f"Start with iteration {iterations} (queue length: {len(hole_options)} + {len(hole_options_next_round)})."
        )
        if oracle is None:
            oracle = self._analyse_from_scratch(self._open_constants, hole_options[0], set())
        else:
            self._analyse_sub_options(oracle, hole_options[0])
        return iterations, oracle, oracle.decided(self.thresholds)

    def run_partitioning(self):
        """

        :return: 
        """

        if self.input_has_multiple_properties():
            raise RuntimeError("Lifting is only implemented for single properties")

        if self.input_has_restrictions():
            raise RuntimeError("Restrictions are not supported by quotient based approaches")

        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)

        self._open_constants = self.holes

        options_above = []
        nr_options_above = 0
        options_below = []
        nr_options_below = 0
        oracle = None
        iterations = 0

        hole_options = [self.hole_options]
        total_nr_options = self.hole_options.size()
        logger.info(f"Total number of options: {total_nr_options}")
        hole_options_next_round = []
        self.use_oracle = True
        while True:
            iterations, oracle, threshold_synthesis_result = self._perform_analysis(
                iterations, hole_options, hole_options_next_round, oracle
            )

            if threshold_synthesis_result == dynasty.jani.quotient_container.ThresholdSynthesisResult.UNDECIDED:
                logger.debug("Undecided.")

                if hole_options[0].size() > 2:
                    oracle.scheduler_color_analysis()
                    hole_options_next_round += self._split_hole_options(hole_options[0], oracle)
                else:
                    hole_options_next_round += self._split_hole_options(hole_options[0], None)

            else:
                if threshold_synthesis_result == ThresholdSynthesisResult.ABOVE:
                    logger.debug("All above.")
                    options_above.append(hole_options[0])
                    nr_options_above += hole_options[0].size()

                else:
                    logger.debug("All below.")

                    options_below.append(hole_options[0])
                    nr_options_below += hole_options[0].size()

            remaining = total_nr_options - nr_options_above - nr_options_below
            logger.info(
                f"Number options above {nr_options_above} (in {len(options_above)} regions) "
                f"and below {nr_options_below} (in {len(options_below)} regions). Remaining: {remaining}"
            )
            logger.info(f"Singleton regions {oracle.dtmcs_checked}")
            logger.info(
                f"Critical timings so far: {oracle.build_time} building, "
                f"{oracle.mc_time} checking {oracle.sched_ana_time} analysis."
            )
            hole_options = hole_options[1:]
            if len(hole_options) == 0:
                if len(hole_options_next_round) == 0:
                    break
                logger.info("Next round...")
                if len(hole_options_next_round) * 8 > remaining:
                    self.use_oracle = False
                hole_options = hole_options_next_round
                hole_options_next_round = []
        return options_above, options_below

    def _split_hole_options(self, hole_options, oracle):

        def split_list(a_list):
            half = len(a_list) // 2
            return a_list[:half], a_list[half:]

        # Where to split.
        splitters = []
        selected_splitter = None
        one_side_list = None
        other_side_list = None

        if oracle is not None and self.use_oracle:
            selected_splitter, one_side_list, other_side_list = oracle.propose_split()
            logger.debug(f"Oracle proposes a split at {selected_splitter}")

        if not isinstance(one_side_list, Iterable):
            one_side_list = [one_side_list]
        if not isinstance(other_side_list, Iterable):
            other_side_list = [other_side_list]

        logger.debug(f"Proposed (pre)split: {one_side_list} vs. {other_side_list}")

        if selected_splitter is None:
            # Split longest.
            maxlength = 0
            for k, v in hole_options.items():
                maxlength = max(maxlength, len(v))
                if len(v) == maxlength:
                    selected_splitter = k
            if maxlength == 1:
                raise RuntimeError("Undecided result, but cannot split")

        options = hole_options[selected_splitter]
        logger.debug(f"Splitting {[str(val) for val in options]}...")
        assert len(options) > 1, "Cannot split along {}".format(selected_splitter)

        one_values = [self.hole_options[selected_splitter][one_side] for one_side in one_side_list if
                      one_side is not None]
        other_values = [self.hole_options[selected_splitter][other_side] for other_side in other_side_list if
                        other_side is not None]
        logger.debug(f"Pre-splitted {one_values} and {other_values}")
        remaining_options = [x for x in options if x not in one_values + other_values]
        logger.debug(f"Now distribute {remaining_options}")
        second, first = split_list(remaining_options)
        # if one_side is not None:
        first = first + one_values
        # if other_side is not None:
        second = second + other_values
        splitters.append([selected_splitter, first, second])

        logger.info(
            f"Splitting {selected_splitter} into {'[' + ','.join([str(x) for x in first]) + ']'} "
            f"and {'[' + ','.join([str(x) for x in second]) + ']'}"
        )

        # Split.
        assert len(splitters) == 1
        split_queue = [hole_options]
        for splitter in splitters:
            new_split_queue = []
            for options in split_queue:
                new_split_queue.append(HoleOptions(options))
                new_split_queue[-1][splitter[0]] = splitter[1]
                new_split_queue.append(HoleOptions(options))
                new_split_queue[-1][splitter[0]] = splitter[2]
            split_queue = new_split_queue
        assert len(split_queue) == 2
        return split_queue


class AllInOneChecker(QuotientBasedFamilyChecker):
    """

    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._open_constants = []

    def get_quotient_container(self):
        if self.input_has_restrictions():
            raise RuntimeError("All-in-one currently cannot support restrictions")

        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes
        logger.info(f"Total number of options: {self.hole_options.size()}")

        return self._analyse_from_scratch(
            self._open_constants, self.hole_options, self._open_constants.keys()
        )

    def run_feasibility(self):
        if self.input_has_optimality_property():
            return self._run_optimal_feasibility()
        if self.input_has_multiple_properties():
            raise RuntimeError("All-in-one is only implemented for single properties")

        quotient_container = self.get_quotient_container()
        logger.info(f"Result obtained... now compare with {self.thresholds}")
        result = quotient_container.decided(self.thresholds[0])
        assert result != ThresholdSynthesisResult.UNDECIDED, "All-in-one should not yield undecided result"
        if self._accept_if_above[0]:
            return result == ThresholdSynthesisResult.ABOVE, None, None
        else:
            assert not self._accept_if_above[0]
            return result == ThresholdSynthesisResult.BELOW, None, None

    def _run_optimal_feasibility(self):
        if self.input_has_multiple_properties():
            raise RuntimeError("All-in-one with optimal feasibility is only implemented for single properties")
        quotient_container = self.get_quotient_container()
        obtained_bound = quotient_container.lower_bound() if self._optimality_setting.direction == "min" else \
            quotient_container.upper_bound()
        return True, None, obtained_bound


class OneByOneChecker(QuotientBasedFamilyChecker):
    """

    TODO: strictly, this class is not based on lifting (but the code depends on mc_formulae for historical reasons
    """

    def run_feasibility(self):
        jani_program = self.sketch
        iteration = 0
        iter_start = time.time()
        model_states_cum = 0
        model_transitions_cum = 0
        total_nr_options = self.hole_options.size()
        for constant_assignment in itertools.product(*self.hole_options.values()):
            iteration += 1
            logger.info(f"Iteration: {iteration} / {total_nr_options}")
            constants = [jani_program.get_constant(c).expression_variable for c in self.hole_options.keys()]
            substitution = dict(zip(constants, constant_assignment))
            instance = jani_program.define_constants(substitution)
            mh = ModelHandling()

            mh.build_model(instance, self.mc_formulae, self.mc_formulae_alt)
            model_states_cum += mh.full_mdp.nr_states
            model_transitions_cum += mh.full_mdp.nr_transitions
            index = 0
            mh.mc_model(index)

            logger.info("Ran for {}, expect total: {}".format(time.time() - iter_start, (
                    time.time() - iter_start) * total_nr_options / iteration))
            logger.info(f"Avg model size {model_states_cum} states, {model_transitions_cum} transition")
            # TODO something with result


class ConsistentSchedChecker(QuotientBasedFamilyChecker):
    """
    Enumerate over all schedulers.

    Supports (only) threshold synthesis as of now. 
    """

    def run_partitioning(self):
        return self._run(mode=2)

    def run_feasibility(self):
        if self.input_has_optimality_property():
            return self._run(mode=1)
        else:
            return self._run()

    def _run(self, mode=0):
        """

        :param mode: 0 feasibility, 1 optimal feasibility, 2 partitioning
        :return:
        """

        # TODO dont use integers for mode.
        prep_start = time.time()
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes
        if mode == 1:
            self._set_optimality_setting()

        iterations = 0

        total_nr_options = self.hole_options.size()
        logger.info(f"Total number of options: {total_nr_options}")
        oracle = self.jani_quotient_builder.construct(self.hole_options, set(), set())
        oracle.prepare(self.mc_formulae, self.mc_formulae_alt)
        oracle.get_full_colors()
        prep_end = time.time()
        prep_time = prep_end - prep_start
        above = []
        below = []

        best_result = None
        total_states = 0
        total_transitions = 0

        iter_start = time.time()
        for selected_hole_option_dict in itertools.product(*self.hole_options.values()):
            selected_hole_option = HoleOptions(
                [(x, [y]) for x, y in zip(self.hole_options.keys(), selected_hole_option_dict)])
            iterations += 1
            logger.info(f"Start with iteration {iterations}.")
            self._analyse_sub_options(oracle, selected_hole_option)
            if mode == 0:
                # Plain feasibility checking.
                threshold_synthesis_results = oracle.decided(self.thresholds)
                for index, result in enumerate(threshold_synthesis_results):
                    if result == ThresholdSynthesisResult.ABOVE and self._accept_if_above[index]:
                        if index == len(threshold_synthesis_results) - 1:
                            return True, selected_hole_option.pick_one_in_family(), None, iterations
                    elif result == ThresholdSynthesisResult.BELOW and not self._accept_if_above[index]:
                        if index == len(threshold_synthesis_results) - 1:
                            return True, selected_hole_option.pick_one_in_family(), None, iterations
                    else:
                        break
            elif mode == 1:
                # Optimal feasibility checking.
                threshold_synthesis_result = oracle.decided(self.thresholds)
                if threshold_synthesis_result == ThresholdSynthesisResult.ABOVE and \
                        self._optimality_setting.direction == "max":
                    self.thresholds[0] = oracle.upper_bound()
                    best_result = selected_hole_option.pick_one_in_family()
                if threshold_synthesis_result == ThresholdSynthesisResult.BELOW and \
                        self._optimality_setting.direction == "min":
                    self.thresholds[0] = oracle.lower_bound()
                    best_result = selected_hole_option.pick_one_in_family()
            elif mode == 2:
                threshold_synthesis_result = oracle.decided(self.thresholds)
                if threshold_synthesis_result == ThresholdSynthesisResult.ABOVE:
                    above.append(selected_hole_option)
                if threshold_synthesis_result == ThresholdSynthesisResult.BELOW:
                    below.append(selected_hole_option)

            logger.info("Ran for {}, expect total up to: {}".format(prep_time + time.time() - iter_start, prep_time + (
                    time.time() - iter_start) * total_nr_options / iterations))
            total_states += oracle.mdp_handling.mdp.nr_states
            total_transitions += oracle.mdp_handling.mdp.nr_transitions
            logger.info(
                f"Average states so far {total_states / iterations}. "
                f"Average transitions so far {total_transitions / iterations}"
            )

        if mode == 0:
            return False, None, None, 0
        elif mode == 1:
            return best_result is not None, best_result, self.thresholds[0], iterations
        else:
            return above, below
