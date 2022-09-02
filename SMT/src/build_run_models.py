import sys
sys.path.append("./")

from utils.smt_utils import run_model, check_smt_parameters


data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}


if __name__ == "__main__":
    params = check_smt_parameters(data_path['txt'])
    solver_name = params['solver_name']
    instance_file = params['instance_val']
    timeout = params['timeout']
    rotation = params['rotation']
    verbose = params['verbose']
    test_range = params['test']
    logic = "LIA"

    if test_range is not None:
        solutions = []

        for i in range(test_range[0], test_range[1] + 1):
            inst_file = f'ins-{i}.txt'
            inst_sol, inst_time = run_model(solver_name, inst_file, timeout, rotation, verbose, logic)

            if inst_sol is not None:
                solutions.append({'instance':i, 'l': inst_sol['l'], 'time': inst_time})
        
        for el in solutions:
            print(f"Found solution l={el['l']} for instance {el['instance']} in {el['time']} seconds.")
    else:
        solution, ex_time = run_model(solver_name, instance_file, timeout, rotation, verbose, logic)
        
        if solution is not None:
            print(f"Minimum found l is {solution['l']}, found in {round(ex_time, 4)} seconds.")
        else:
            print("No solutions found for this instance.")
