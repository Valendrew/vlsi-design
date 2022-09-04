from distutils.command.config import config
import logging
import sys
sys.path.append("./")

from typing import List, Tuple, Union
from utils.cp_utils import (
    check_cp_admissable_timeout,
    check_cp_solver_exists,
    parse_cp_argument,
)

from utils.manage_paths import format_plot_file, format_statistic_file
from utils.solution_log import print_logging, save_solution
from utils.smt_utils import extract_input_from_txt
from utils.plot import plot_solution
from utils.manage_statistics import checking_instances, save_statistics
from utils.types import (
    SOLUTION_ADMISSABLE,
    ModelType,
    RunType,
    SolverMinizinc,
)
from utils.minizinc_solver import run_minizinc


run_type: RunType = RunType.CP
root_path = "./CP"
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}


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

    print_logging(sol, verbose)
    plot_solution(sol, plot_file)
    W, N, widths, heights = extract_input_from_txt(data_path["txt"], f"{input_name}.txt")
    l = sol.height if hasattr(sol, "height") else 0
    cx = sol.coords['x'] if hasattr(sol, "coords") else []
    cy = sol.coords['y'] if hasattr(sol, "coords") else []
    save_solution(root_path, model_type.value, f"{input_name}.txt", (W, N, l, widths, heights, cx, cy))

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
    vprint = print if verbose else lambda *a, **k: None
    test_iterator = checking_instances(test_instances)
    statistics_path = format_statistic_file(
        run_type, test_instances, model_type, solver=solver.value
    )

    for i in test_iterator:
        sol = compute_solution(
            f"ins-{i}", model_type, solver, timeout, free_search, verbose
        )
        save_statistics(statistics_path, sol)
        vprint(
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
    test_mode = parser_args["testing"]

    # Check if the solver is installed in the user's system
    if not check_cp_solver_exists(solver):
        logging.error(f"{solver.name} not available in the current system")
        sys.exit(2)

    # Check if the timeout is out of range
    if not check_cp_admissable_timeout(timeout):
        logging.error("Timeout out of range")
        sys.exit(2)

    if test_mode is not None:
        test_instances = (test_mode[0], test_mode[1])
        compute_tests(test_instances, model_type, solver, free_search, timeout, verbose)
    else:
        sol = compute_solution(input_name, model_type, solver, timeout, free_search, verbose)

