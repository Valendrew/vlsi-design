from os.path import join as join_path
import math
import z3

import sys
sys.path.append("./")

from utils.smt_utils import extract_input_from_txt

root_path = "./SMT"
plot_path = join_path(root_path, "out/plots/{model}/{file}")
statistics_path = join_path(root_path, "out/statistics/{model}/{file}.csv")
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}


# We append to the string all the script to avoid writing it manually
def build_model(W, N, widths, heights):
    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i]*heights[i] for i in range(N)]) / W)
    l_up = sum(heights)
    lines = []

    lines.append("(declare-fun coord_x (Int) Int)")
    lines.append("(declare-fun coord_y (Int) Int)")
    #lines.append("(declare-fun l () Int)")

    # Domain of variables
    lines += [f"(assert (and (>= (select coord_x {i}) 0) (<= (select coord_x {i}) {W-min(widths)})))" for i in range(N)]
    lines += [f"(assert (and (>= (select coord_y {i}) 0) (<= (select coord_y {i}) {l_up-min(heights)})))" for i in range(N)]
    lines.append(f"(assert (and (>= l {l_low}) (<= l {l_up})))")


    # Non-Overlap constraints, at least one needs to be satisfied
    for i in range(N):
        for j in range(N):
            if i < j:
                lines.append(f"(assert (or (<= (+ (select coord_x {i}) {widths[i]}) (select coord_x {j})) "
                                         f"(<= (+ (select coord_y {i}) {heights[i]}) (select coord_y {j})) "
                                         f"(>= (- (select coord_x {i}) {widths[j]}) (select coord_x {j})) "
                                         f"(>= (- (select coord_y {i}) {heights[i]}) (select coord_y {j}))))"
                            )


    # Boundary constraints
    lines += [f"(assert (and (<= (+ (select coord_x {i}) {widths[i]}) {W}) (<= (+ (select coord_y {i}) {heights[i]}) l)))" for i in range(N)]


    lines.append("(check-sat)")
    #lines.append(f"(get-value ({' '.join([f'(select pos {i})' for i in range(N)])}))")
    
    with open(f"{root_path}/src/model.smt2", "w+") as f:
        for line in lines:
            f.write(line + '\n')
    


def run_solver():
    solver = z3.Optimize()
    l = z3.Int("l")
    solver.add(l)
    smt_mod = z3.parse_smt2_file(f"{root_path}/src/model.smt2")
    solver.add(smt_mod)
    solver.minimize(l)
    

if __name__ == "__main__":
    W, N, widths, heights = extract_input_from_txt(data_path["txt"], "ins-10.txt")
    build_model(W, N, widths, heights)
    solver = z3.Optimize()
    run_solver()