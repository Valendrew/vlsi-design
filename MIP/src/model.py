import sys
sys.path.append("./")

import logging
import math
from typing import List, Tuple, Union

from utils.manage_paths import format_data_file, format_plot_file, format_statistic_file
from utils.manage_statistics import checking_instances, save_statistics
from utils.mip_utils import (
    build_mip_solution,
    check_mip_admissable_timeout,
    check_mip_solver_exists,
    configure_cplex_solver,
    configure_mosek_solver,
    parse_mip_argument,
)
from utils.solution_log import print_logging, save_solution
from utils.smt_utils import extract_input_from_txt
from utils.plot import plot_solution
from utils.minizinc_solver import run_minizinc
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

from create_model import build_pulp_model, build_pulp_rotation_model

run_type: RunType = RunType.MIP


def run_mip_solver(
    input_name: str,
    model_type: ModelType,
    solver: SolverMIP,
    timeout: int,
    configuration=None,
):
    sol = Solution()
    data_file = format_data_file(input_name, InputMode.TXT)
    W, N, widths, heights = extract_input_from_txt(data_file.rsplit("/", maxsplit=1)[1])

    sol.input_name = input_name
    sol.width = W
    sol.n_circuits = N
    sol.circuits = [[widths[i], heights[i]] for i in range(N)]

    # Model selection
    if model_type == ModelType.BASE:
        prob = build_pulp_model(W, N, widths, heights)
    elif model_type == ModelType.ROTATION:
        prob = build_pulp_rotation_model(W, N, widths, heights)
    else:
        raise BaseException("Model type not available")

    if solver == SolverMIP.CPLEX:
        solver = configure_cplex_solver(timeout, configuration)
    elif solver == SolverMIP.MOSEK:
        solver = configure_mosek_solver(timeout)
    else:
        raise BaseException("Solver not available")

    try:
        prob.solve(solver)
    except BaseException as err:
        logging.error(f"Unexpected {err}")
        sol.status = StatusEnum.ERROR
        return sol

    sol.status = StatusEnum(prob.sol_status)
    sol.solve_time = prob.solutionTime

    if SOLUTION_ADMISSABLE(sol.status):
        if prob.solutionTime > timeout:
            sol.status = StatusEnum.FEASIBLE
        sol = build_mip_solution(prob, sol, N, model_type)
        """ sol.height = round(l)

        rotation = [False] * N
        coords = {"x": [None] * N, "y": [None] * N}
        for v in prob.variables():
            if round(v.varValue) > 0 and str(v.name).startswith("place"):
                circuit, pos =  [int(val) for val in v.name[6:].split("_")]
                coords["x"][circuit] = round(positions[pos][1][0])
                coords["y"][circuit] = round(positions[pos][1][1])

        sol.coords = coords

        sol.rotation = rotation if model_type == ModelType.ROTATION else None """
    return sol


def compute_solution(
    input_name: str,
    model_type: ModelType,
    solver: SolverMIP,
    timeout: int,
    verbose: bool,
    configuration=None,
):
    # plot path
    plot_file = format_plot_file(run_type, input_name, model_type)

    if solver == SolverMIP.MINIZINC:
        if model_type == ModelType.ROTATION:
            raise BaseException("Rotation model has not been implemented")
        mz_solver = SolverMinizinc.CPLEX
        free_search = False

        data_file = format_data_file(input_name, InputMode.TXT)
        W, N, widths, heights = extract_input_from_txt(data_file.rsplit("/", maxsplit=1)[1])

        res_timeout = timeout
        height_opt = max(
            max(heights), math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
        )
        while res_timeout > 0:
            sol = run_minizinc(
                input_name,
                run_type,
                model_type,
                mz_solver,
                res_timeout,
                free_search,
                height=height_opt,
            )

            res_timeout -= sol.solve_time
            sol.solve_time = timeout - res_timeout
            if not SOLUTION_ADMISSABLE(sol.status):
                height_opt += 1
            else:
                res_timeout = 0
                

    elif solver == SolverMIP.MOSEK or solver == SolverMIP.CPLEX:
        sol = run_mip_solver(input_name, model_type, solver, timeout, configuration)

    print_logging(sol, verbose)
    plot_solution(sol, plot_file)

    return sol


def compute_tests(
    test_instances: Union[Tuple[int], List[int]],
    model_type: ModelType,
    solver: SolverMIP,
    timeout: int,
    verbose: bool,
    configuration=None,
):
    test_iterator = checking_instances(test_instances)
    statistics_path = format_statistic_file(
        run_type, test_instances, model_type, solver=solver.value
    )

    for i in range(len(test_iterator)):
        input_name = f"ins-{test_iterator[i]}"
        sol = compute_solution(
            input_name,
            model_type,
            solver,
            timeout,
            verbose,
            configuration[i] if configuration else None,
        )
        save_statistics(
            statistics_path, sol, configuration[i] if configuration else None
        )
        print(
            f"- Computed instance {test_iterator[i]}: {sol.status.name}{f' in time {sol.solve_time}' if SOLUTION_ADMISSABLE(sol.status) else ''}"
        )
        if SOLUTION_ADMISSABLE(sol.status):
            widths = [i[0] for i in sol.circuits]
            heights = [i[0] for i in sol.circuits]

            save_solution(
                run_type.value,
                model_type.value,
                input_name + ".txt",
                (
                    sol.width,
                    sol.n_circuits,
                    sol.height,
                    widths,
                    heights,
                    sol.coords["x"],
                    sol.coords["y"],
                ),
            )


if __name__ == "__main__":
    parser_args = parse_mip_argument()
    input_name: str = parser_args["instance"]
    model_type: ModelType = ModelType(parser_args["model"])
    solver: SolverMIP = SolverMIP(parser_args["solver"])
    timeout: int = parser_args["timeout"]
    verbose: bool = parser_args["verbose"]
    test_mode = parser_args["testing"]

    # Check if the solver is installed in the user's system
    if not check_mip_solver_exists(solver):
        logging.error(f"{solver.name} not available in the current system")
        sys.exit(2)

    # Check if the timeout is out of range
    if not check_mip_admissable_timeout(timeout):
        logging.error("Timeout out of range")
        sys.exit(2)

    if test_mode is not None:
        
        configuration = None
        test_instances = (test_mode[0], test_mode[1])
        compute_tests(
            test_instances,
            model_type,
            solver,
            timeout,
            verbose,
            configuration=configuration,
        )
    else:
        compute_solution(input_name, model_type, solver, timeout, verbose)
