import argparse
import time
from os.path import exists, join, splitext

from utils.types import ModelType

import z3
import numpy as np

txt_instances = "./vlsi-instances/txt-instances"

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
def z3_parse_solution(data, model_type):
    # Sort the array considering the number of the variables in order to pair x and y
    sort_key = lambda x: int(x[0][7:])
    sort_key_rot = lambda x: int(x[0][3:])

    pairs = dict([(str(m), str(data[m()])) for m in data])
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
                    w, h = data.split(" ")
                    circuits.append((w, h.rstrip()))
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
    p.add_argument('-sol', '--solver', dest='solver_name', help='The name of the solver you want to use [z3, cvc4, mathsat].',
                    type=str, required=True)
    p.add_argument('-rot', '--rotation', dest='rotation', help='True if you want to use the model that considers rotation',
                    action='store_true')
    p.add_argument('-log', '--logic', dest='logic', help='The logic you want to use during the solve.', required=False, 
                    default="LIA")
    p.add_argument('-ins', '--instance-file', dest='instance_val', help='The file of the instance you want to solve.', 
                    type=lambda x: check_file(p, x, data_path), required=True)
    p.add_argument('-to', '--timeout', dest='timeout', help='The maximum number of seconds after which the solve is interrupted.', 
                    type=int, default=300)
    p.add_argument('-v', '--verbose', dest='verbose', help='If the function has to print different information about the solve.', 
                    action='store_true')

    args = p.parse_args()
    param = dict(args._get_kwargs())
    return param


# It returns the solution found by the solver on the current formula
def run_solver_once(solver, model_type, verbose):
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
            new_timeout = int(timeout*1000-(check_time-start_time)*1000)
            if new_timeout < 0:
                vprint("Timeout reached, search stopped.")
                return opt_sol, timeout
            solver.set("timeout", new_timeout)

        curr_l = opt_sol['l'] if 'l' in opt_sol else l_up
        curr_sol = run_solver_once(solver, model_type, verbose)
        if curr_sol != None:
            if curr_sol['solution']['l'] < curr_l:
                opt_sol = curr_sol['solution']
                vprint(f"Found solution with l={opt_sol['l']}, low={low} - up={up}")
            l_var = curr_sol['l_var']
            up = l_guess
            # Add constraints to l
            vprint(f"Add constraint l < {up}.")
            solver.add(l_var() < up)
        else:
            low = l_guess + 1
            vprint(f"No solutions found in the last run.")
        i += 1
    end_time = time.perf_counter()

    return opt_sol, (end_time-start_time)
