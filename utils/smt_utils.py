import argparse
import time, math, warnings
from os.path import exists, join, splitext

import sys 
sys.path.append('./')

from utils.types import ModelType, SolverSMT, Solution, StatusEnum
from utils.plot import plot_cmap
from utils.solution_log import save_solution
from utils.manage_statistics import save_statistics

from pysmt.shortcuts import LT, Int, Solver, Equals
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.smtlib.parser import SmtLib20Parser

txt_instances = "./vlsi-instances/txt-instances"
root_path = './SMT'
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}
plot_path = join(root_path, "out/{model}/plots/{file}")


def extract_input_from_txt(data_path, file_instance):
    data_file = data_path.format(file=file_instance)
    with open(data_file, 'r') as fin:
        text = [line.rstrip() for line in fin.readlines()]
            
    W, N = int(text.pop(0)), int(text.pop(0))
    widths, heights = [], []
    for val in text:
        w, h = val.split()
        widths.append(int(w))
        heights.append(int(h))
    return W, N, widths, heights


# Parse the solution returned by the z3 solver
def parse_solution(data, model_type):
    # Sort the array considering the number of the variables in order to pair x and y
    sort_key = lambda x: int(x[0][7:])
    sort_key_rot = lambda x: int(x[0][3:])

    pairs = dict([(str(m[0]), str(m[1])) for m in data])
    coord_x = sorted([(n, v) for n, v in pairs.items() if n.startswith("coord_x")], key=sort_key)
    coord_y = sorted([(n, v) for n, v in pairs.items() if n.startswith("coord_y")], key=sort_key)
    rotation = sorted([(n, v) for n, v in pairs.items() if n.startswith("rot")], key=sort_key_rot) if model_type == ModelType.ROTATION.value else None
    
    l = int(pairs['l'])
    coord_x = [val[1] for val in coord_x]
    coord_y = [val[1] for val in coord_y]
    rotation = [True if val[1] == "True" else False for val in rotation] if rotation is not None else None
    return l, coord_x, coord_y, rotation


# It returns widths and heights from the txt instance 
def get_w_and_h_from_txt(file_name):
    complete_path = join(txt_instances, file_name)
    if exists(complete_path):
        circuits = []
        with open(complete_path) as fin:
            for i, data in enumerate(fin.readlines()):
                if i != 0 and i != 1:
                    data = data.split(" ")
                    circuits.append((data[0], data[1].rstrip()))
        return circuits
    else:
        print("ERROR: the instance path doesn't exists.")


# Check if the file with the weights exists and if it has the correct extension
def check_file(parser, path, data_path):
    ext = splitext(path)[-1].lower()

    if ext != '.txt' :
        parser.error(f"The file has not the correct extension: {ext} must be .txt")
    else:
        if exists(data_path.format(file=path)):
            return path
        else:
            parser.error(f"The instance file doesn't exist in the current path: {data_path.format(file=path)}.")


# Check the parameters given to the script
def check_smt_parameters(data_path):
    p = argparse.ArgumentParser()
    mode = p.add_mutually_exclusive_group(required=True)

    p.add_argument('-sol', '--solver', dest='solver_name', help='The name of the solver you want to use [z3, cvc4].',
                    type=str, required=True, choices=[SolverSMT.Z3.value, SolverSMT.CVC4.value])
    p.add_argument('-rot', '--rotation', dest='rotation', help='True if you want to use the model that considers rotation',
                    action='store_true')
    mode.add_argument('-ins', '--instance-file', dest='instance_val', help='The file of the instance you want to solve.', 
                    type=lambda x: check_file(p, x, data_path))
    p.add_argument('-to', '--timeout', dest='timeout', help='The maximum number of seconds after which the solve is interrupted.', 
                    type=int, default=300)
    p.add_argument('-v', '--verbose', dest='verbose', help='If the function has to print different information about the solve.', 
                    action='store_true')
    mode.add_argument('-test', '--test-smt', dest='test', help='Specify the interval of instances to run the solver on.', 
                    nargs=2, type=int)
    p.add_argument('-search', '--search-method', dest='search', help='Choose the search method to optimize the solution.',
                    type=str, choices=['bin', 'lbound'], default="bin")
    args = p.parse_args()
    param = dict(args._get_kwargs())
    return param


# We append to the string all the script to avoid writing it manually
def build_SMTLIB_model(W, N, widths, heights, logic="LIA"):
    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i]*heights[i] for i in range(N)]) / W)
    l_up = sum(heights)
    lines = []

    # Options
    lines.append(f"(set-logic {logic})")

    # Variables declaration
    lines += [f"(declare-fun coord_x{i} () Int)" for i in range(N)]
    lines += [f"(declare-fun coord_y{i} () Int)" for i in range(N)]
    lines.append("(declare-fun l () Int)")

    # Domain of variables
    lines += [f"(assert (and (>= coord_x{i} 0) (<= coord_x{i} {W-min(widths)})))" for i in range(N)]
    lines += [f"(assert (and (>= coord_y{i} 0) (<= coord_y{i} {l_up-min(heights)})))" for i in range(N)]
    lines.append(f"(assert (and (>= l {l_low}) (<= l {l_up})))")


    # Non-Overlap constraints, at least one needs to be satisfied
    for i in range(N):
        for j in range(N):
            if i < j:
                lines.append(f"(assert (or (<= (+ coord_x{i} {widths[i]}) coord_x{j}) "
                                         f"(<= (+ coord_y{i} {heights[i]}) coord_y{j}) "
                                         f"(>= (- coord_x{i} {widths[j]}) coord_x{j}) "
                                         f"(>= (- coord_y{i} {heights[j]}) coord_y{j})))"
                )

    # Boundary constraints
    lines += [f"(assert (and (<= (+ coord_x{i} {widths[i]}) {W}) (<= (+ coord_y{i} {heights[i]}) l)))" for i in range(N)]

    
    # Cumulative constraints 
    for w in widths:
        sum_var = [f"(ite (and (<= coord_y{i} {w}) (< {w} (+ coord_y{i} {heights[i]}))) {widths[i]} 0)" for i in range(N)]
        lines.append(f"(assert (<= (+ {' '.join(sum_var)}) {W}))")

    for h in heights:
        sum_var = [f"(ite (and (<= coord_x{i} {h}) (< {h} (+ coord_x{i} {widths[i]}))) {heights[i]} 0)" for i in range(N)]
        lines.append(f"(assert (<= (+ {' '.join(sum_var)}) l))")

    # Symmetry breaking same size 
    for i in range(N):
        for j in range(N):
            if i < j:
                lines.append(f"(assert (ite (and (= {widths[i]} {widths[j]}) (= {heights[i]} {heights[j]})) (<= coord_x{i} coord_x{j}) true))")
    

    # Symmetry breaking that inserts the circuit with the maximum area in (0, 0)
    areas = [widths[i]*heights[i] for i in range(N)]
    max_area_ind = areas.index(max(areas))
    lines.append(f"(assert (= coord_x{max_area_ind} 0))")
    lines.append(f"(assert (= coord_y{max_area_ind} 0))")

    lines.append("(check-sat)")
    for i in range(N):
        lines.append(f"(get-value (coord_x{i}))")
        lines.append(f"(get-value (coord_y{i}))")
    lines.append("(get-value (l))")
    
    with open(f"{root_path}/src/model.smt2", "w+") as f:
        for line in lines:
            f.write(line + '\n')

    return l_up


# We append to the string all the script to avoid writing it manually
def build_SMTLIB_model_rot(W, N, widths, heights, logic="LIA"):
    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i]*heights[i] for i in range(N)]) / W)
    l_up = sum([max(heights[i], widths[i]) for i in range(N)])
    lines = []

    # Options
    lines.append(f"(set-logic {logic})")

    # Variables declaration
    lines += [f"(declare-fun coord_x{i} () Int)" for i in range(N)]
    lines += [f"(declare-fun coord_y{i} () Int)" for i in range(N)]
    lines += [f"(declare-fun rot{i} () Bool)" for i in range(N)]
    lines += [f"(declare-fun w_real{i} () Int)" for i in range(N)]
    lines += [f"(declare-fun h_real{i} () Int)" for i in range(N)]

    lines.append("(declare-fun l () Int)")

    # Domain of variables
    coord_up = min(widths + heights)
    lines += [f"(assert (and (>= coord_x{i} 0) (<= coord_x{i} {W-coord_up})))" for i in range(N)]
    lines += [f"(assert (and (>= coord_y{i} 0) (<= coord_y{i} {l_up-coord_up})))" for i in range(N)]
    lines += [f"(assert (ite rot{i} (= w_real{i} {heights[i]}) (= w_real{i} {widths[i]})))" for i in range(N)]
    lines += [f"(assert (ite rot{i} (= h_real{i} {widths[i]}) (= h_real{i} {heights[i]})))" for i in range(N)]

    lines.append(f"(assert (and (>= l {l_low}) (<= l {l_up})))")

    # Boundary constraints
    lines += [f"(assert (and (<= (+ coord_x{i} w_real{i}) {W}) (<= (+ coord_y{i} h_real{i}) l)))" for i in range(N)]

    # Non-Overlap constraints, at least one needs to be satisfied
    for i in range(N):
        for j in range(N):
            if i < j:
                lines.append(f"(assert (or (<= (+ coord_x{i} w_real{i}) coord_x{j}) "
                                         f"(<= (+ coord_y{i} h_real{i}) coord_y{j}) "
                                         f"(>= (- coord_x{i} w_real{j}) coord_x{j}) "
                                         f"(>= (- coord_y{i} h_real{j}) coord_y{j})))"
                )

    # Cumulative constraints 
    for w in widths:
        sum_var = [f"(ite (and (<= coord_y{i} {w}) (< {w} (+ coord_y{i} h_real{i}))) w_real{i} 0)" for i in range(N)]
        lines.append(f"(assert (<= (+ {' '.join(sum_var)}) {W}))")

    for h in heights:
        sum_var = [f"(ite (and (<= coord_x{i} {h}) (< {h} (+ coord_x{i} w_real{i}))) h_real{i} 0)" for i in range(N)]
        lines.append(f"(assert (<= (+ {' '.join(sum_var)}) l))")
    
    # Symmetry breaking same size 
    for i in range(N):
        for j in range(N):
            if i < j:
                lines.append(f"(assert (ite (and (= {widths[i]} {widths[j]}) (= {heights[i]} {heights[j]})) (< coord_x{i} coord_x{j}) true))")
    
    # Symmetry breakings for rotation
    lines += [f"(assert (= rot{i} false))" for i in range(N) if widths[i] == heights[i]]
    lines += [f"(assert (= rot{i} false))" for i in range(N) if heights[i] > W]

    # Symmetry breaking that inserts the circuit with the maximum area in (0, 0)
    areas = [widths[i]*heights[i] for i in range(N)]
    max_area_ind = areas.index(max(areas))
    lines.append(f"(assert (= coord_x{max_area_ind} 0))")
    lines.append(f"(assert (= coord_y{max_area_ind} 0))")

    lines.append("(check-sat)")
    for i in range(N):
        lines.append(f"(get-value (coord_x{i}))")
        lines.append(f"(get-value (coord_y{i}))")
        lines.append(f"(get-value (rot{i}))")
    lines.append("(get-value (l))")
    
    with open(f"{root_path}/src/model_rot.smt2", "w+") as f:
        for line in lines:
            f.write(line + '\n')

    return l_up


# It returns the solution found by the solver on the current formula
def run_solver_once(solver, model_type, verbose):
    vprint = print if verbose else lambda *a, **k: None

    solution = {"solution":{}, "l_var": None}

    res = solver.solve()
    if res != True:
        vprint("Unsat therefore search interrupted.")
        return None

    last_model = solver.get_model()
    var_list = [v[0] for v in last_model]
    l_ind = [str(v) for v in var_list].index('l')
    l_var = var_list[l_ind]
    l, coord_x, coord_y, rotation = parse_solution(last_model, model_type)

    solution['solution'] = {'l': l, 'coord_x': coord_x, 'coord_y': coord_y , 'rotation': rotation}
    solution['l_var'] = l_var

    return solution


# Offline OMT implementation for finding the minimum value of l
def offline_omt(solver, l_low, l_up, model_type, timeout, verbose):
    vprint = print if verbose else lambda *a, **k: None

    low, up = l_low, l_up
    opt_sol = {}

    start_time = time.perf_counter()
    i = 0
    # Start binary search
    while low < up:
        l_guess = (low + up)//2

        if i > 0:
            check_time = time.perf_counter()
            remained_time = int(timeout*1000-(check_time-start_time)*1000)
            if remained_time < 0:
                vprint("Timeout reached, search stopped.")
                return opt_sol, timeout

        curr_l = opt_sol['l'] if 'l' in opt_sol else l_up
        try: 
            curr_sol = run_solver_once(solver, model_type, verbose)
        except SolverReturnedUnknownResultError:
            vprint("Timeout reached, search stopped.")
            return opt_sol, timeout

        if curr_sol != None:
            if curr_sol['solution']['l'] < curr_l:
                opt_sol = curr_sol['solution']
            vprint(f"Found solution with l={curr_sol['solution']['l']}, low={low} - up={up}")
            l_var = curr_sol['l_var']
            up = l_guess
            # Add constraints to l
            vprint(f"Add constraint l < {up}.")
            solver.add_assertion(LT(l_var, Int(up)))
        else:
            low = l_guess + 1
            vprint(f"No solutions found in the last run.")
        i += 1
    end_time = time.perf_counter()

    return opt_sol, (end_time-start_time)


# Apply a search starting from the minimum value of the l
def low_bound_search(solver, parser, l_low, model_type, model_filename, timeout, verbose):
    symb = list(parser.get_script_fname(model_filename).get_declared_symbols())
    ind_l = [str(m) for m in symb].index('l')
    l_var = symb[ind_l]
    l_guess = l_low
    solution = {}

    solver.push()
    solver.add_assertion(Equals(l_var, Int(l_guess)))
    start_time = time.perf_counter()
    try: 
        while not solver.solve():
            l_guess = l_low  + 1
            solver.pop()
            solver.push()
            solver.add_assertion(Equals(l_var, Int(l_guess)))
            if verbose:
                print(f"Add constraint l={l_guess}")
        end_time = time.perf_counter()
    except SolverReturnedUnknownResultError:
        print("Timeout reached, search stopped.")
        return solution, timeout

    model = solver.get_model()
    l, coord_x, coord_y, rotation = parse_solution(model, model_type)
    solution = {'l': l, 'coord_x': coord_x, 'coord_y': coord_y, 'rotation': rotation}
    return solution, (end_time-start_time)


def run_model(solver_name, instance_file, timeout, rotation, verbose, logic, search_method, stat_file):
    W, N, widths, heights = extract_input_from_txt(data_path["txt"], instance_file)
    l_low = math.ceil(sum([widths[i]*heights[i] for i in range(N)]) / W)

    vprint = print if verbose else lambda *a, **k: None

    if rotation:
        model_type = ModelType.ROTATION.value
        model_filename = "model_rot.smt2"
        vprint("Generating the rotation model\n")
        l_up = build_SMTLIB_model_rot(W, N, widths, heights, logic=logic)
    else:
        model_type = ModelType.BASE.value
        model_filename = "model.smt2"
        vprint("Generating the base model\n")
        l_up = build_SMTLIB_model(W, N, widths, heights, logic=logic)

    plot_file = plot_path.format(model=model_type, file=instance_file.split(".")[0])
    # Set some solution object variables
    solution_obj = Solution()
    solution_obj.input_name=instance_file[:-4]
    solution_obj.width=W
    solution_obj.n_circuits=N,
    solution_obj.circuits=[[widths[i], heights[i]] for i in range(N)]
    solution_obj.configuration = None

    if solver_name == SolverSMT.CVC4.value:
        solver_options = {'tlimit': timeout*1000} 
    else:
        solver_options = {'timeout': timeout*1000, 'auto_config': True} 
        warnings.filterwarnings("ignore")
        
    solver = Solver(name=solver_name, solver_options=solver_options)
    parser = SmtLib20Parser()
    complete_path_model = f'./SMT/src/{model_filename}'
    formula = parser.get_script_fname(complete_path_model).get_strict_formula()

    solver.add_assertion(formula)
    if search_method == "lbound":
        solution = low_bound_search(solver, parser, l_low, model_type, complete_path_model, timeout, verbose)
    else:
        solution = offline_omt(solver, l_low, l_up, model_type, timeout, verbose)

    if len(solution[0].keys()) != 0:
        l, coord_x, coord_y, rotation = solution[0]['l'], solution[0]['coord_x'], solution[0]['coord_y'],  solution[0]['rotation']
        solution_obj.coords = {'x': coord_x, 'y': coord_y}
        solution_obj.height = l
        solution_obj.rotation = rotation
        solution_obj.solve_time = solution[1]
        solution_obj.status = StatusEnum.FEASIBLE
        plot_cmap(
            W, l, N, get_w_and_h_from_txt(instance_file), {'x': coord_x, 'y': coord_y},
                plot_file, rotation=rotation, cmap_name="turbo_r"
        )
        save_solution(root_path, model_type, instance_file, (W, N, l, widths, heights, coord_x, coord_y))
        save_statistics(stat_file, solution_obj)
        return solution
    else:
        print(f"No solution found, something goes wrong.")
        return None, 0

