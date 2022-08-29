import argparse
from os.path import exists, join, splitext

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

    args = p.parse_args()
    param = dict(args._get_kwargs())
    return param