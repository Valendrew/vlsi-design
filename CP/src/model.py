from distutils.command.config import config
from os.path import join as join_path

from utils.formatting import format_plot_file, format_statistic_file
from utils.logging import print_logging


from utils.plot import plot, plot_cmap
from utils.manage_statistics import save_statistics
from utils.types import ModelType, RunType, SolverMinizinc, InputMode
from utils.minizinc_solver import run_minizinc

run_type: RunType = RunType.CP


def compute_solution(
    input_name: str,
    input_mode: InputMode,
    model_type: ModelType,
    solver: SolverMinizinc,
    timeout: int,
    free_search: bool,
    verbose: bool,
):
    # plot path
    plot_file = format_plot_file(run_type, input_name, model_type)

    sol, result = run_minizinc(
        input_name,
        run_type,
        input_mode,
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

    return sol, result


# Compute the solution for the desired number of instances and with the desired solver
# TODO move as a decorator function for other solvers
def compute_tests(
    test_instances,
    input_mode: InputMode,
    model_type: ModelType,
    solver: SolverMinizinc,
    timeout: int,
    free_search: bool,
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
        sol, result = compute_solution(
            f"ins-{i}", input_mode, model_type, solver, timeout, free_search, verbose
        )
        print(f"- Computed a solution for instance {i}.")
        save_statistics(statistics_path, result, i)


if __name__ == "__main__":
    # TODO change as input of script
    input_name: str = "ins-5"
    input_mode = InputMode.DZN
    model_type: ModelType = ModelType.BASE
    solver = SolverMinizinc.CHUFFED
    free_search = True

    # optional inputs
    verbose: bool = True
    timeout: int = 300

    # TODO add specific type
    test_range = (1, 10)
    save_stats = True

    if save_stats:
        compute_tests(
            (1, 20),
            input_mode,
            model_type,
            solver,
            timeout,
            free_search,
            verbose,
        )
    else:
        compute_solution(
            input_name, input_mode, model_type, solver, timeout, free_search, verbose
        )
