import math, time
from os.path import join as join_path

import sys
sys.path.append("./")

from utils.smt_utils import extract_input_from_txt, get_w_and_h_from_txt, check_smt_parameters
from utils.plot import plot_cmap

from pysmt.shortcuts import Symbol, INT, And, GE, LE, Int, Or, Solver, NotEquals, get_env
from pysmt.logics import LIA, QF_IDL

root_path = "./SMT"
plot_path = join_path(root_path, "out/plots/{model}/{file}")
statistics_path = join_path(root_path, "out/statistics/{model}/{file}.csv")
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}

solvers_path = {
    "mathsat": "C:\\Users\\danie\\.smt_solvers\\msat\\mathsat-5.6.1-win64-msvc\\bin\\mathsat.exe",
    "cvc4": "C:\\Users\\<name>\\.smt_solvers\\<solver-dir>\\<path-to-exe>\\cvc4.exe",
}

def build_base_model(W, N, widths, heights):
    l_low = math.ceil(sum([widths[i]*heights[i] for i in range(N)]) / W)
    l_up = sum(heights)

    # Variables
    coord_x = [Symbol(f"coord_x{i}", INT) for i in range(N)]
    coord_y = [Symbol(f"coord_y{i}", INT) for i in range(N)]
    l = Symbol("l", INT)

    constraints = []
    # Domains restriction
    constraints += [And(GE(coord_x[i], Int(0)), LE(coord_x[i], Int(W - min(widths)))) for i in range(N)]
    constraints += [And(GE(coord_y[i], Int(0)), LE(coord_y[i], Int(l_up - min(heights)))) for i in range(N)]
    constraints.append(And(GE(l, Int(l_low)), LE(l, Int(l_up))))

    # Constrain within the W and the found l
    constraints += [And((LE(coord_x[i] + widths[i], Int(W))), (LE(coord_y[i] + heights[i], l))) for i in range(N)]

    # Avoid overlapping 
    for i in range(N):
        for j in range(N):
            if i < j:
                constraints.append(Or(LE(coord_x[i] + widths[i], coord_x[j]),
                                      LE(coord_y[i] + heights[i], coord_y[j]),
                                      GE(coord_x[i] - widths[j], coord_x[j]),
                                      GE(coord_y[i] - heights[j], coord_y[j]),
                            ))

    formula = And(*constraints)
    return formula, (l, coord_x, coord_y)



def run_solver(name, logic, formula, vars, solver_options, l_up):
    l_var, cx_var, cy_var = vars
    timeout = solver_options['timeout'] if 'timeout' in solver_options else 300

    solver = Solver(name=name, logic=logic, solver_options=solver_options)
    solver.add_assertion(formula)

    start_time = time.perf_counter()
    solution = {'l': l_up, 'coord_x':[], 'coord_y':[]}
    while True:
        check_time = time.perf_counter()
        if (check_time-start_time) > timeout:
            print("Timeout: search interrupted.")
            break
        res = solver.solve()
        if res:
            model = solver.get_model()
            l = model.get_value(l_var).constant_value()   
            if l < solution['l']:
                coord_x =[int(str(model.get_value(cx))) for cx in cx_var]
                coord_y =[int(str(model.get_value(cy))) for cy in cy_var]
                solution = {'l': l, 'coord_x':coord_x, 'coord_y': coord_y}
            solver.add_assertion(NotEquals(l_var, Int(l)))
        else:
            print('Search is terminated.')
            break
    if solution['l'] == l_up:
        print("No solutions found")
    
    return solution
    


if __name__ == "__main__":
    params = check_smt_parameters(data_path['txt'])
    solver_name = params['solver_name']
    logic = params['logic']
    instance_file = params['instance_val']
    timeout = params['timeout']
    rotation = params['rotation']
    allowed_logics = [LIA, QF_IDL]

    W, N, widths, heights = extract_input_from_txt(data_path['txt'], instance_file)
    if not rotation:
        formula, vars = build_base_model(W, N, widths, heights)
    else:
        print("Not supported yet")
        #formula, vars = build_rotation_model(W, N, widths, heights)

    if solver_name not in ['z3', 'cvc4', 'mathsat']:
        print("Solver not supported")
        sys.exit(0)

    if solver_name != 'z3':
        sol_path = solvers_path[solver_name]
        env = get_env()
        env.factory.add_generic_solver(solver_name, sol_path, allowed_logics)

        solution = run_solver(solver_name, logic, formula, vars, solver_options={}, l_up=sum(heights))
        print(solution)
    else:
        solution = run_solver(solver_name, logic, formula, vars, solver_options={"timeout":timeout*1000}, l_up=sum(heights))
        print(solution)
    #plot_cmap(W, sol['l'], N, get_w_and_h_from_txt(instance_file), {'x':sol['coord_x'],'y':sol['coord_y']}, "./ins-15.png", rotation=None, cmap_name="Set3")'''

