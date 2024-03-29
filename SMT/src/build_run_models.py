import sys
sys.path.append("./")

from utils.smt_utils import run_model, check_smt_parameters
from utils.types import ModelType, RunType, StatisticMode
from utils.manage_paths import format_statistic_file


run_type = RunType.SMT 

if __name__ == "__main__":
    params = check_smt_parameters()
    solver_name = params['solver_name']
    instance_file = params['instance_val']
    timeout = params['timeout']
    rotation = params['rotation']
    verbose = params['verbose']
    test_range = params['test']
    search_method = params['search']
    logic = "LIA"

    model_type = ModelType.ROTATION if rotation else ModelType.BASE
    if test_range is not None:

        stat_file = format_statistic_file(run_type, test_range, model_type, StatisticMode.CSV, solver_name)
        solutions = []

        for i in range(test_range[0], test_range[1] + 1):
            inst_file = f'ins-{i}.txt'
            inst_sol, inst_time = run_model(solver_name, inst_file, timeout, rotation, verbose, logic, search_method, stat_file)

            if inst_sol is not None:
                solutions.append({'instance':i, 'l': inst_sol['l'], 'time': inst_time})
        
        for el in solutions:
            if verbose:
                print(f"Found solution l={el['l']} for instance {el['instance']} in {el['time']} seconds.")
    else:
        inst_num = int(instance_file[4:-4])
        stat_file = format_statistic_file(run_type, (inst_num, inst_num), model_type, StatisticMode.CSV, solver_name)
        solution, ex_time = run_model(solver_name, instance_file, timeout, rotation, verbose, logic, search_method, stat_file)
        
        if solution is not None:
            print(f"Minimum found l is {solution['l']}, found in {round(ex_time, 4)} seconds.")
        else:
            print("No solutions found for this instance.")
