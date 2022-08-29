import pulp as pl
from pulp import CPLEX_PY, MOSEK
from utils.formatting import format_data_file, format_plot_file
from utils.logging import print_logging
from utils.smt_utils import extract_input_from_txt
from os.path import join as join_path
import math
import sys
from utils.plot import plot_cmap
from utils.minizinc_solver import run_minizinc
from utils.types import (
    InputMode,
    ModelType,
    Solution,
    SolverMinizinc,
    SolverMIP,
    RunType,
    StatusEnum,
)

run_type: RunType = RunType.MIP


# We append to the string all the script to avoid writing it manually
def build_pulp_model(W: int, N: int, widths, heights):
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


def run_mip_solver(
    input_name: str, model_type: ModelType, solver: SolverMIP, timeout: int
):
    sol = Solution
    # TODO change to take only data_file
    data_file = format_data_file(input_name, InputMode.TXT)
    W, N, widths, heights = extract_input_from_txt(
        "./vlsi-instances/txt-instances/{file}", input_name + ".txt"
    )

    sol.input_name = input_name
    sol.width = W
    # FIXME change to proper solve time
    sol.solve_time = 0
    sol.n_circuits = N
    sol.circuits = [[widths[i], heights[i]] for i in range(N)]
    sol.rotation = None if model_type == ModelType.ROTATION else None

    prob: pl.LpProblem = build_pulp_model(W, N, widths, heights)
    solver = pl.getSolver(solver.value)
    if solver == SolverMIP.CPLEX:
        solver = CPLEX_PY(timeout=timeout)
    elif solver == SolverMIP.MOSEK:
        # FIXME mosek doesn't have a timeout
        solver = MOSEK()

    prob.solve(solver)

    if prob.status:
        sol.status = StatusEnum.OPTIMAL

    sol.height = int(pl.value(prob.objective))
    coords = {"x": [None] * N, "y": [None] * N}
    for v in prob.variables():
        # print(v.name)
        if "coord_x" in v.name:
            ind = int(v.name.split("coord_x_")[1])
            coords["x"][ind] = int(v.varValue)
        elif "coord_y" in v.name:
            ind = int(v.name.split("coord_y_")[1])
            coords["y"][ind] = int(v.varValue)

    sol.coords = coords
    return sol


if __name__ == "__main__":
    # TODO change as input of script
    input_name: str = "ins-3"
    model_type: ModelType = ModelType.BASE

    # solvers
    # solver: SolverMIP = SolverMIP.MINIZINC
    # solver: SolverMIP = SolverMIP.MOSEK
    solver: SolverMIP = SolverMIP.CPLEX

    # optional inputs
    verbose: bool = True
    timeout: int= 300

    # plot path
    plot_file = format_plot_file(
        run_type, input_name, model_type, solver=solver.name.lower()
    )

    if solver == SolverMIP.MINIZINC:
        input_mode = InputMode.DZN
        mz_solver = SolverMinizinc.CHUFFED
        free_search = True

        sol, _ = run_minizinc(
            input_name,
            run_type,
            input_mode,
            model_type,
            mz_solver,
            timeout,
            free_search,
        )
    elif solver == SolverMIP.MOSEK or solver == SolverMIP.CPLEX:
        sol = run_mip_solver(input_name, model_type, solver, timeout)

    if verbose:
        print_logging(sol)
    plot_cmap(
        sol.width,
        sol.height,
        sol.n_circuits,
        sol.circuits,
        sol.coords,
        plot_file,
        sol.rotation,
        "turbo_r",
    )
