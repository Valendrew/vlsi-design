import re
import json
from os.path import exists, join

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
def z3_parse_solution(data):
    # Sort the array considering the number of the variables in order to pair x and y
    sort_key = lambda x: int(x[0][7:])

    pairs = dict([(str(m), str(data[m()])) for m in data])
    coord_x = sorted([(n, v) for n, v in pairs.items() if n.startswith("coord_x")], key=sort_key)
    coord_y = sorted([(n, v) for n, v in pairs.items() if n.startswith("coord_y")], key=sort_key)

    l = int(pairs['l'])
    coord_x = [val[1] for val in coord_x]
    coord_y = [val[1] for val in coord_y]

    return l, coord_x, coord_y


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
