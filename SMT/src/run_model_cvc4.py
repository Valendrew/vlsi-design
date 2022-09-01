import math, time
from os.path import join as join_path

import sys
sys.path.append("./")

from utils.smt_utils import extract_input_from_txt, get_w_and_h_from_txt, check_smt_parameters, z3_parse_solution
from utils.plot import plot_cmap
from utils.types import ModelType


from pysmt.shortcuts import Symbol, INT, And, GE, LE, Int, Or, Solver, NotEquals, get_env, LT
from pysmt.smtlib.parser import SmtLib20Parser
from pysmt.logics import LIA, QF_IDL


root_path = "./SMT"
plot_path = join_path(root_path, "out/{model}/plots/{file}")
statistics_path = join_path(root_path, "out/statistics/{model}/cvc4_{file}.csv")
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}


def run_solver(solv, logic, solver_options={}):
    # It returns the solution found by the solver on the current formula
    vprint = print if verbose else lambda *a, **k: None

    if model_type == ModelType.BASE.value:
        solution = {"solution":{"l": 0, "coord_x":[], "coord_y":[]}, "l_var": None}
    else:
        solution = {"solution":{"l": 0, "coord_x":[], "coord_y":[], "rotation": []}, "l_var": None}

    res = solver.check()
    if res == z3.unsat:
        vprint("Unsat therefore search interrupted.")
        return None
    if res == z3.unknown:
        if solver.reason_unknown() == "timeout":
            vprint("Timeout reached, search stopped.")
            return None
        else:
            vprint("Error during the search, unknown status returned.")
            return None

    last_model = solver.model()
    l_ind = [str(m) for m in last_model].index('l')
    l_var = last_model[l_ind]
    
    l, coord_x, coord_y, rotation = z3_parse_solution(last_model, model_type)
    solution['solution'] = {'l': l, 'coord_x': coord_x, 'coord_y': coord_y , 'rotation': rotation}
    solution['l_var'] = l_var

    return solution


def run_cvc4_model(name, rotation, model_file, inputs, solver_options):

    W, N, widths, heights = inputs

    solver = Solver(name=name, solver_options=solver_options)
    parser = SmtLib20Parser()
    formula = parser.get_script_fname(model_file).get_strict_formula()
    symb = list(parser.get_script_fname("model.smt2").get_declared_symbols())

    solver.add_assertion(formula)
    if rotation:
        solution = {'l': 0, 'coord_x': [], 'coord_y': [], 'rotation': []}
    else:
        solution = {'l': 0, 'coord_x': [], 'coord_y': []}

    start_time = time.perf_counter()
    while True:
        res = solver.solve()
        if res:
            last_model = solver.get_model()
            l, cx, cy, rotation = z3_parse_solution(last_model)
            if l < solution[0]:
                solution = (l, cx, cy)
            if time.perf_counter() - start_time > 25:
                break
            solver.reset_assertions()
            solver.add_assertion(formula)
            solver.add_assertion(NotEquals(symb[-1], Int(l)))
        else:
            break

    return 0
    solver = z3.Solver()
    solver.set(timeout=timeout*1000)
    formula = z3.parse_smt2_file(f"{root_path}/src/{model_filename}")
    solver.add(formula)

    l_low = math.ceil(sum([widths[i]*heights[i] for i in range(N)]) / W)
    
    solution = offline_omt(solver, l_low, l_up, model_type, timeout, verbose)
    if len(solution[0].keys()) != 0:
        l, coord_x, coord_y, rotation = solution[0]['l'], solution[0]['coord_x'], solution[0]['coord_y'],  solution[0]['rotation']
        sol_time = solution[1]
        print(f"Minimum found l is {l}, found in {round(sol_time, 4)} seconds.")
        plot_cmap(
            W, l, N, get_w_and_h_from_txt(instance_file), {'x': coord_x, 'y': coord_y},
                plot_file, rotation=rotation, cmap_name="Set3"
        )
        save_solution(root_path, model_type, instance_file, (W, N, l, widths, heights, coord_x, coord_y))
    else:
        print(f"Something goes wrong.")
        sys.exit(1)         
