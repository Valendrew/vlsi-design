from typing import Tuple
from minizinc import Instance, Model, Solver, Result, Status
from utils.manage_paths import format_data_file, format_model_file
from utils.solution_log import Solution
from utils.types import (
    SOLUTION_ADMISSABLE,
    InputMode,
    ModelType,
    RunType,
    SolverMinizinc,
    StatusEnum,
)
from datetime import timedelta


def compute_solve_time(ex_time: float) -> str:
    magnitude = "s"
    if (ex_time) < 0.01:
        ex_time *= 1000
        magnitude = "ms"

    return f"{ex_time:.6f} {magnitude}"


def get_minizinc_solution(
    result: Result, instance: Instance, sol: Solution
) -> Solution:
    # solutions
    sol.coords = {"x": result.solution.coord_x, "y": result.solution.coord_y}
    sol.height = result.solution.l

    # inputs
    sol.circuits = instance.__getitem__("CIRCUITS")
    sol.n_circuits = instance.__getitem__("N")
    sol.width = instance.__getitem__("W")
    sol.rotation = None if not hasattr(result.solution, "rot") else result.solution.rot

    ex_time = (
        result.statistics["solveTime"].total_seconds()
        + result.statistics["initTime"].total_seconds()
    )
    sol.solve_time = compute_solve_time(ex_time)
    return sol


def run_minizinc(
    input_name: str,
    run_type: RunType,
    model_type: ModelType = ModelType.BASE,
    solver: SolverMinizinc = SolverMinizinc.GECODE,
    timeout: int = None,
    free_search=False,
) -> Solution:
    data_file = format_data_file(input_name, InputMode.DZN)
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
    sol = Solution()
    sol.input_name = input_name

    if result.status == Status.ERROR:
        sol.status = StatusEnum.ERROR
    elif result.status == Status.UNKNOWN:
        sol.status = StatusEnum.NO_SOLUTION_FOUND
    elif result.status == Status.UNBOUNDED:
        sol.status = StatusEnum.UNBOUNDED
    elif result.status == Status.UNSATISFIABLE:
        sol.status = StatusEnum.INFEASIBLE
    elif result.status == Status.SATISFIED:
        sol.status = StatusEnum.FEASIBLE
    elif result.status == Status.OPTIMAL_SOLUTION:
        sol.status = StatusEnum.OPTIMAL
    else:
        raise BaseException("Status not handled")

    if SOLUTION_ADMISSABLE(sol.status):
        return get_minizinc_solution(result, instance, sol)
    else:
        return sol
