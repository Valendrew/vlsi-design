from typing import Tuple
from minizinc import Instance, Model, Solver, Result
from utils.formatting import format_data_file, format_model_file
from utils.logging import Solution, print_logging
from utils.types import InputMode, ModelType, RunType, SolverMinizinc, StatusEnum
from datetime import timedelta


def compute_solve_time(result: Result) -> str:
    ex_time = (
        result.statistics["solveTime"].total_seconds()
        + result.statistics["initTime"].total_seconds()
    )

    magnitude = "s"
    if (ex_time) < 0.01:
        ex_time *= 1000
        magnitude = "ms"

    return f"{ex_time} {magnitude}"


def get_minizinc_solution(
    result: Result, instance: Instance, input_name: str
) -> Solution:
    sol = Solution

    sol.status = StatusEnum.OPTIMAL
    sol.input_name = input_name

    # solutions
    sol.coords = {"x": result.solution.coord_x, "y": result.solution.coord_y}
    sol.height = result.solution.l

    # inputs
    sol.circuits = instance.__getitem__("CIRCUITS")
    sol.n_circuits = instance.__getitem__("N")
    sol.width = instance.__getitem__("W")
    sol.rotation = None if not hasattr(result.solution, "rot") else result.solution.rot

    sol.solve_time = compute_solve_time(result)
    return sol


def run_minizinc(
    input_name: str,
    run_type: RunType,
    input_mode: InputMode = InputMode.DZN,
    model_type: ModelType = ModelType.BASE,
    solver: SolverMinizinc = SolverMinizinc.GECODE,
    timeout: int = None,
    free_search=False,
) -> Tuple[Result, Solution]:
    data_file = format_data_file(input_name, input_mode)
    model_file = format_model_file(run_type, model_type)

    model = Model(model_file)
    solver = Solver.lookup(solver.value)
    instance = Instance(solver, model)
    instance.add_file(data_file, parse_data=True)
    if timeout:
        td_timeout = timedelta(seconds=timeout)
    else:
        td_timeout = None

    result = instance.solve(timeout=td_timeout, free_search=free_search)

    # After the instance has been solved
    if result.status.OPTIMAL_SOLUTION:
        # no solution found
        if not hasattr(result, "solution") or (result.solution is None):
            # TODO handle statistics when -1 is returned
            sol = Solution
            sol.status = StatusEnum.NO_SOLUTION
            return sol

        return get_minizinc_solution(result, instance, input_name), result
