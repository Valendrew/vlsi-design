import pulp as pl
from pulp import CPLEX_PY
from utils.smt_utils import extract_input_from_txt
from os.path import join as join_path
import math
import sys
from utils.plot import plot_cmap


root_path = "./MIP"
plot_path = join_path(root_path, "out/plots/{model}/{file}")
statistics_path = join_path(root_path, "out/statistics/{model}/{file}.csv")
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}
sys.path.append("./")


# We append to the string all the script to avoid writing it manually
def build_model(W, N, widths, heights):
    # LpVariable() for new variables
    # LpProblem() for new problems
    prob = pl.LpProblem("vlsi", pl.LpMinimize)

    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
    l_up: int = sum(heights)

    # Height variable
    l = pl.LpVariable("l", lowBound=l_low, upBound=l_up, cat=pl.LpInteger)
    prob += l

    # Coordinate variables
    set_N = range(N)
    cx_up = W - min(widths)
    cy_up = l_up - min(heights)
    coord_x = pl.LpVariable.dicts(
        "coord_x", indices=set_N, lowBound=0, upBound=cx_up, cat=pl.LpInteger
    )
    coord_y = pl.LpVariable.dicts(
        "coord_y", indices=set_N, lowBound=0, upBound=cy_up, cat=pl.LpInteger
    )

    # Booleans for OR condition
    set_C = range(4)
    delta = pl.LpVariable.dicts("delta", indices=(set_N, set_N, set_C), cat=pl.LpBinary)

    # Non-Overlap constraints, at least one needs to be satisfied
    for i in set_N:
        for j in set_N:
            prob += (
                delta[i][j][0] + delta[i][j][1] + delta[i][j][2] + delta[i][j][3] <= 3
            )

            if i < j:
                prob += coord_x[i] + widths[i] <= coord_x[j] + delta[i][j][0] * W
                prob += coord_x[j] + widths[j] <= coord_x[i] + delta[i][j][1] * W
                prob += coord_y[i] + heights[i] <= coord_y[j] + delta[i][j][2] * l_up
                prob += coord_y[j] + heights[j] <= coord_y[i] + delta[i][j][3] * l_up

    # Boundary constraints
    for i in set_N:
        prob += coord_x[i] + widths[i] <= W
        prob += coord_y[i] + heights[i] <= l
    return prob


if __name__ == "__main__":
    input_name = "ins-15"
    W, N, widths, heights = extract_input_from_txt(
        data_path["txt"], input_name + ".txt"
    )

    prob: pl.LpProblem = build_model(W, N, widths, heights)
    solver = CPLEX_PY(timeLimit=300)
    prob.solve(solver)
    print("Status: ", pl.LpStatus[prob.status])
    height = int(pl.value(prob.objective))
    print(f"Height: {height}")
    # TODO obtain coord_x and coord_y for plotting
    coords = {"x": [None] * N, "y": [None] * N}
    for v in prob.variables():
        # print(v.name)
        if "coord_x" in v.name:
            ind = int(v.name.split("coord_x_")[1])
            coords["x"][ind] = int(v.varValue)
        elif "coord_y" in v.name:
            ind = int(v.name.split("coord_y_")[1])
            coords["y"][ind] = int(v.varValue)

    circuits = [[widths[i], heights[i]] for i in range(N)]
    plot_cmap(
        W, height, N, circuits, coords, plot_path.format(model="base", file=input_name)
    )

    # access info from cplex api object
    # prob.solverModel
