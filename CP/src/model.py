from distutils.command.config import config
import logging
from os.path import join as join_path
import sys
from typing import List, Tuple, Union
from utils.cp_utils import (
    check_cp_admissable_timeout,
    check_cp_solver_exists,
    parse_cp_argument,
)

from utils.manage_paths import format_plot_file, format_statistic_file
from utils.solution_log import print_logging


from utils.plot import plot, plot_cmap
from utils.manage_statistics import checking_instances, save_statistics
from utils.types import (
    SOLUTION_ADMISSABLE,
    ModelType,
    RunType,
    SolverMinizinc,
)
from utils.minizinc_solver import run_minizinc

run_type: RunType = RunType.CP


def compute_solution(
    input_name: str,
    model_type: ModelType,
    solver: SolverMinizinc,
    timeout: int,
    free_search: bool,
    verbose: bool,
):
    # plot path
    plot_file = format_plot_file(run_type, input_name, model_type)

    sol = run_minizinc(
        input_name,
        run_type,
        model_type,
        solver,
        timeout,
        free_search,
    )

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

    return sol


# Compute the solution for the desired number of instances and with the desired solver
def compute_tests(
    test_instances: Union[Tuple[int], List[int]],
    model_type: ModelType,
    solver: SolverMinizinc,
    free_search: bool,
    timeout: int,
    verbose: bool,
):
    test_iterator = checking_instances(test_instances)
    statistics_path = format_statistic_file(
        run_type, test_instances, model_type, solver=solver.value
    )

    for i in test_iterator:
        sol = compute_solution(
            f"ins-{i}", model_type, solver, timeout, free_search, verbose
        )
        save_statistics(statistics_path, sol)
        print(
            f"\n- Computed instance {i}: {sol.status.name} {f'in time {sol.solve_time}' if SOLUTION_ADMISSABLE(sol.status) else ''}"
        )


if __name__ == "__main__":
    parser_args = parse_cp_argument()
    input_name: str = parser_args["instance"]
    model_type: ModelType = ModelType(parser_args["model"])
    solver: SolverMinizinc = SolverMinizinc(parser_args["solver"])
    free_search: bool = parser_args["freesearch"]
    timeout: int = parser_args["timeout"]
    verbose: bool = parser_args["verbose"]
    save_stats: bool = parser_args["statistics"]

    # Check if the solver is installed in the user's system
    if not check_cp_solver_exists(solver):
        logging.error(f"{solver.name} not available in the current system")
        sys.exit(2)

    # Check if the timeout is out of range
    if not check_cp_admissable_timeout(timeout):
        logging.error("Timeout out of range")
        sys.exit(2)

    if save_stats:
        # TODO pass instances through cmd line
        test_instances = (1, 5)
        compute_tests(test_instances, model_type, solver, free_search, timeout, verbose)
    else:
        compute_solution(input_name, model_type, solver, free_search, timeout, verbose)
