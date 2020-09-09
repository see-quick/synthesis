import json
import subprocess
import sys

PARAMS = {"param": 0, "time": 1, "iters": 2, "sat": 3}
# CASE_STUDIES = {"grid": "40", "pole": "5", "maze": "50", "dpm": "12", "herman": "2", "bsn": 0}
CASE_STUDIES = {"grid": "40"}
MODES = {1: "threshold", 2: "cegar_iters_limit", 3: "cegis_expanded_per_iter"}
EXPERIMENT_SCRIPT = "workspace/experiments/experiment.sh"
LOG_FILE = "workspace/experiments/log_grep.txt"
METHODS = ["research", "lift", "cegis"]

ITERATIONS = {"grid": 4, "pole": 4, "maze": 4, "dpm": 2, "herman": 2, "bsn": 4}
BILATERAL = ["dpm", "herman"]

property_kinds = ["liveness", "safety"]
PROPERTY_KINDS = {
    "grid": property_kinds, "pole": property_kinds, "maze": property_kinds,
    "dpm": ["safety"], "herman": ["liveness"], "bsn": ["liveness"]
}

# START, STOP, STEP
default_limits = \
    {"threshold": [0.00, 1.00, 0.01], "cegar_iters_limit": [0, 50, 2], "cegis_expanded_per_iter": [0, 500, 10]}
LIMITS = {
    "dpm": {"threshold": [0.00, 0.10, 0.001], "cegar_iters_limit": [0, 50, 2], "cegis_expanded_per_iter": [0, 500, 10]},
    "grid": default_limits, "pole": default_limits, "maze": default_limits,
    "herman": default_limits, "bsn": default_limits
}

DEFAULT_LIMITS = {
    "grid": {"threshold": 0.5, "cegar_iters_limit": 1, "cegis_expanded_per_iter": 50},
    "pole": {"threshold": 0.5, "cegar_iters_limit": 3, "cegis_expanded_per_iter": 10},
    "maze": {"threshold": 0.5, "cegar_iters_limit": 1, "cegis_expanded_per_iter": 70},
    "dpm": {"threshold": 0.5, "cegar_iters_limit": 1, "cegis_expanded_per_iter": 500},
    "herman": {"threshold": 0.5, "cegar_iters_limit": 1, "cegis_expanded_per_iter": 10},
    "bsn": {"threshold": 0.5, "cegar_iters_limit": 1, "cegis_expanded_per_iter": 100},
}


def get_name(case_study):
    return case_study.split('-')[0]


def call_experiment_script(case_study, mode, method, threshold, cegar_iters_limit, cegis_expanded_per_iter):
    stop = LIMITS[get_name(case_study)][MODES[mode]][1]
    step = LIMITS[get_name(case_study)][MODES[mode]][2]
    print(
        f"Exploring {MODES[mode]} for {case_study}: "
        f"from {LIMITS[get_name(case_study)][MODES[mode]][0]} to {stop} with {step} step."
    )
    return subprocess.run(
        [
            "./" + EXPERIMENT_SCRIPT, str(method), str(mode), case_study, CASE_STUDIES[get_name(case_study)],
            str(threshold), str(cegar_iters_limit), str(cegis_expanded_per_iter), str(stop), str(step)
        ],
        stdout=subprocess.DEVNULL
    )


def run_experiment_script(case_study, mode, threshold=None, cegar_iters_limit=None, cegis_expanded_per_iter=None):
    threshold = threshold if threshold is not None else DEFAULT_LIMITS[get_name(case_study)]["threshold"]
    cegar_iters_limit = cegar_iters_limit if cegar_iters_limit is not None else \
        DEFAULT_LIMITS[get_name(case_study)]["cegar_iters_limit"]
    cegis_expanded_per_iter = cegis_expanded_per_iter if cegis_expanded_per_iter is not None else \
        DEFAULT_LIMITS[get_name(case_study)]["cegis_expanded_per_iter"]

    call_experiment_script(case_study, mode, "research", threshold, cegar_iters_limit, cegis_expanded_per_iter)
    log_file = open(LOG_FILE, "r")
    log_file.readline()  # skip first empty line
    return log_file


def explore_thresholds(case_study):
    for line in run_experiment_script(case_study, 1):
        params = [v.strip() for v in line.split(',')]
        if params[PARAMS["sat"]] == "False" and case_study.split('-')[1] == property_kinds[0]:
            return float(params[PARAMS["param"]]) - LIMITS[get_name(case_study)]["threshold"][2]  # - no pole, herman
        elif params[PARAMS["sat"]] == "True" and case_study.split('-')[1] == property_kinds[1]:
            return float(params[PARAMS["param"]]) - LIMITS[get_name(case_study)]["threshold"][2]  # - yes dpm


def explore_time_depend_param(case_study, mode, threshold, cegar_iters_limit=None):
    cegar_iters_limit = cegar_iters_limit if cegar_iters_limit is not None else \
        DEFAULT_LIMITS[get_name(case_study)]["cegar_iters_limit"]
    min_time = sys.float_info.max
    max_time = sys.float_info.min
    param_value = 1
    for line in run_experiment_script(case_study, mode, threshold, cegar_iters_limit):
        params = [v.strip() for v in line.split(',')]
        if float(params[PARAMS["time"]]) <= min_time:
            min_time = float(params[PARAMS["time"]])
            param_value = int(params[PARAMS["param"]])
        if float(params[PARAMS["time"]]) > max_time:
            max_time = float(params[PARAMS["time"]])
    diff_time = max_time - min_time
    return param_value if diff_time > 0.05 * max_time else \
        (LIMITS[get_name(case_study)][MODES[mode]][1] - LIMITS[get_name(case_study)][MODES[mode]][0]) / 2.0


def get_thresholds(threshold, property_kind, case_study):
    def frange():
        r = start
        while r <= stop:
            yield r
            r = round(r + threshold_step * 2, 4)

    threshold_step = LIMITS[case_study]["threshold"][2]
    print(f"THRESHOLD: {threshold}")
    start = threshold - threshold_step
    if property_kind == "liveness" or case_study in BILATERAL:
        start = start - ITERATIONS[case_study] * threshold_step * 2
    stop = threshold + threshold_step
    if property_kind == "safety" or case_study in BILATERAL:
        stop = stop + ITERATIONS[case_study] * threshold_step * 2
    return frange()


def save_json(dictionary, file_name):
    with open(file_name, "w") as fp:
        json.dump(dictionary, fp)


def load_json(file_name):
    with open(file_name) as fp:
        return json.load(fp)


def explore_parameters():
    params = {}
    for case_study in CASE_STUDIES.keys():
        params[case_study] = {}
        for property_kind in PROPERTY_KINDS[case_study]:
            params[case_study][property_kind] = []
            threshold = explore_thresholds(case_study + "-" + property_kind)
            for threshold in get_thresholds(threshold, property_kind, case_study):
                cegar_iters_limit = explore_time_depend_param(case_study + "-" + property_kind, 2, threshold)
                cegis_expanded_per_iter = explore_time_depend_param(
                    case_study + "-" + property_kind, 3, threshold, cegar_iters_limit
                )
                params[case_study][property_kind].append(
                    {
                        "threshold": threshold,
                        "cegar_iters_limit": cegar_iters_limit,
                        "cegis_expanded_per_iter": cegis_expanded_per_iter
                    }
                )
                print(
                  f"Found cegar_iters_limit: {cegar_iters_limit} and cegis_expanded_per_iter: {cegis_expanded_per_iter}"
                  f" for threshold {threshold} and {case_study + '-'  + property_kind}."
                )
        save_json(params, "workspace/experiments/params/" + case_study + ".json")
        return


def run_experiments(file_name):
    params = load_json(file_name)
    results = {}
    for name, case_study in params.items():
        results[name] = {}
        for property_kind in PROPERTY_KINDS[name]:
            results[name][property_kind] = {}
            for params_assignment in case_study[property_kind]:
                results[name][property_kind][params_assignment["threshold"]] = {}
                for method in METHODS:
                    results[name][property_kind][params_assignment["threshold"]][method] = {}
                    out = subprocess.run(
                        [
                            "./" + EXPERIMENT_SCRIPT, method, "0", name + "-" + property_kind, CASE_STUDIES[name],
                            str(params_assignment["threshold"]),
                            str(params_assignment["cegar_iters_limit"]),
                            str(params_assignment["cegis_expanded_per_iter"])
                        ],
                        stdout=subprocess.PIPE
                    )
                    result = out.stdout.decode("utf-8").strip().split('\n')[-1]
                    time, iters, sat = [v.strip() for v in result.split(',')]
                    results[name][property_kind][params_assignment["threshold"]][method]["time"] = round(float(time), 3)
                    results[name][property_kind][params_assignment["threshold"]][method]["iters"] = iters
        save_json(results, "workspace/experiments/results/" + name + ".json")


if __name__ == '__main__':
    if sys.argv[1] == "0":
        explore_parameters()
    elif sys.argv[1] == "1":
        run_experiments(sys.argv[2])
    else:
        print("Invalid argument value. The supported values are:\n"
              "0: Explore the value of parameters.\n"
              "1: Run experiments for measuring the times."
              )
