import logging
import sys
import pulp
import mosek


from utils.formatting import format_data_file, format_plot_file, format_statistic_file
from utils.mip_utils import check_admissable_timeout, check_mip_solver_exists, parse_mip_argument
from utils.solution_log import print_logging
from utils.smt_utils import extract_input_from_txt
from utils.plot import plot_cmap
from utils.minizinc_solver import compute_solve_time, run_minizinc
from utils.types import (
    SOLUTION_ADMISSABLE,
    InputMode,
    ModelType,
    Solution,
    SolverMinizinc,
    SolverMIP,
    RunType,
    StatusEnum,
)

from create_model import build_pulp_model

run_type: RunType = RunType.MIP


def run_mip_solver(
    input_name: str, model_type: ModelType, solver: SolverMIP, timeout: int
):
    solver_verbose = False

    sol = Solution
    data_file = format_data_file(input_name, InputMode.TXT)
    # TODO change to take only data_file
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
        solver = pulp.CPLEX_CMD(mip=True, msg=solver_verbose, timeLimit=timeout, options=["set preprocessing symmetry -1"], warmStart=True)
    elif solver == SolverMIP.MOSEK:
        options = {
            # mosek.iparam.num_threads: 8,
            mosek.dparam.mio_max_time: timeout,
        }
        solver = pulp.MOSEK(mip=True, msg=solver_verbose, options=options)
    else:
        raise BaseException("Solver not available")

    try:
        prob.solve(solver)
    except BaseException as err:
        print(f"Unexpected {err}")
        sol.status = StatusEnum.ERROR
        return sol

    sol.status = StatusEnum(prob.sol_status)
    sol.solve_time = compute_solve_time(prob.solutionTime)

    if SOLUTION_ADMISSABLE(sol.status):
        sol.height = int(pulp.value(prob.objective))

        coords = {"x": [None] * N, "y": [None] * N}
        for v in prob.variables():
            # print(f"{v.name}: {v.value()}")
            if "coord_x" in v.name:
                ind = int(v.name.split("coord_x_")[1])
                coords["x"][ind] = round(v.varValue)
            elif "coord_y" in v.name:
                ind = int(v.name.split("coord_y_")[1])
                coords["y"][ind] = round(v.varValue)

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
    if SOLUTION_ADMISSABLE(sol.status):
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
    return sol


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
        sol = compute_solution(f"ins-{i}", model_type, solver, timeout, verbose)
        print(
            f"\n- Computed instance {i}: {sol.status.name} {f'in time {sol.solve_time}' if SOLUTION_ADMISSABLE(sol.status) else ''}"
        )

        # TODO save statistics for MIP
        # save_statistics(statistics_path, result, i)


if __name__ == "__main__":
    parser_args = parse_mip_argument()
    # TODO change as input of script
    input_name: str = parser_args["instance"]
    model_type: ModelType = ModelType(parser_args["model"])
    solver: SolverMIP = SolverMIP(parser_args["solver"])
    timeout: int = parser_args["timeout"]
    verbose: bool = parser_args["verbose"]

    # statistics
    save_stats = False

    if not check_mip_solver_exists(solver):
        logging.error(f"{solver.name} not available in the current system")
        sys.exit(2)
    if not check_admissable_timeout(timeout):
        logging.error("Timeout out of range")
        sys.exit(2)
    if save_stats:
        test_instances = [5]
        # test_instances = (1, 40)
        compute_tests(test_instances, model_type, solver, timeout, False)
    else:
        compute_solution(input_name, model_type, solver, timeout, verbose)
