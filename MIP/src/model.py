import math

import pulp
import mosek

from utils.formatting import format_data_file, format_plot_file, format_statistic_file
from utils.logging import print_logging
from utils.smt_utils import extract_input_from_txt
from utils.plot import plot_cmap
from utils.minizinc_solver import compute_solve_time, run_minizinc
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
    prob = pulp.LpProblem("vlsi", pulp.LpMinimize)

    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
    l_up: int = sum(heights)

    # Height variable
    l = pulp.LpVariable("l", lowBound=l_low, upBound=l_up, cat=pulp.LpInteger)
    prob += l

    # Coordinate variables
    set_N = range(N)
    cx_up = W - min(widths)
    cy_up = l_up - min(heights)
    coord_x = pulp.LpVariable.dicts(
        "coord_x", indices=set_N, lowBound=0, upBound=cx_up, cat=pulp.LpInteger
    )
    coord_y = pulp.LpVariable.dicts(
        "coord_y", indices=set_N, lowBound=0, upBound=cy_up, cat=pulp.LpInteger
    )

    # Booleans for OR condition
    set_C = range(4)
    delta = pulp.LpVariable.dicts(
        "delta", indices=(set_N, set_N, set_C), cat=pulp.LpBinary
    )

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
    solver_verbose = False

    sol = Solution
    # TODO change to take only data_file
    data_file = format_data_file(input_name, InputMode.TXT)
    W, N, widths, heights = extract_input_from_txt(
        "./vlsi-instances/txt-instances/{file}", input_name + ".txt"
    )

    sol.input_name = input_name
    sol.width = W
    sol.n_circuits = N
    sol.circuits = [[widths[i], heights[i]] for i in range(N)]
    sol.rotation = None if model_type == ModelType.ROTATION else None

    prob: pulp.LpProblem = build_pulp_model(W, N, widths, heights)

    if solver == SolverMIP.CPLEX:
        solver = pulp.CPLEX_PY(msg=solver_verbose, timeLimit=timeout)
    elif solver == SolverMIP.MOSEK:
        options = {
            # mosek.iparam.num_threads: 8,
            mosek.dparam.mio_max_time: timeout,
        }
        solver = pulp.MOSEK(msg=solver_verbose, options=options)
    else:
        raise BaseException("Solver not available")

    try:
        prob.solve(solver)
    except BaseException as err:
        print(f"Unexpected {err}")
        sol.status = StatusEnum.ERROR
        return sol

    if prob.status == pulp.LpStatusOptimal:
        sol.status = StatusEnum.OPTIMAL
    elif prob.status == pulp.LpStatusNotSolved:
        sol.status = StatusEnum.NOT_SOLVED
    else:
        sol.status = StatusEnum.INFEASIBLE
        return sol

    sol.solve_time = compute_solve_time(prob.solutionTime)
    sol.height = int(pulp.value(prob.objective))
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


def compute_solution(
    input_name: str,
    model_type: ModelType,
    solver: SolverMIP,
    timeout: int,
    verbose: bool,
):
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
    if sol.status in [StatusEnum.NOT_SOLVED, StatusEnum.OPTIMAL]:
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


def compute_tests(
    test_instances,
    model_type: ModelType,
    solver: SolverMIP,
    timeout: int,
    verbose: bool,
):
    output_name = f"{solver.value}_{min(test_instances)}_{max(test_instances)}"

    # If instances must be treated as a range
    if isinstance(test_instances, tuple):
        test_iterator = range(test_instances[0], test_instances[1] + 1)
    # If explicits instances are passed as a list
    elif isinstance(test_instances, list):
        output_name += "_uncontinguous"
        test_iterator = test_instances
    else:
        return -1

    statistics_path = format_statistic_file(run_type, output_name, model_type)

    for i in test_iterator:
        compute_solution(f"ins-{i}", model_type, solver, timeout, verbose)
        print(f"- Computed a solution for instance {i}.\n")
        # TODO save statistics for MIP
        # save_statistics(statistics_path, result, i)


if __name__ == "__main__":
    # TODO change as input of script
    input_name: str = "ins-10"
    model_type: ModelType = ModelType.BASE

    # solvers
    # solver: SolverMIP = SolverMIP.MINIZINC
    solver: SolverMIP = SolverMIP.MOSEK
    # solver: SolverMIP = SolverMIP.CPLEX

    # optional inputs
    verbose: bool = True
    timeout: int = 300

    # statistics
    save_stats = True
    if save_stats:
        test_instances = [10]
        compute_tests(test_instances, model_type, solver, timeout, verbose)
    else:
        compute_solution(input_name, model_type, solver, verbose, timeout)
