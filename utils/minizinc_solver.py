from typing import Tuple
from minizinc import Instance, Model, Solver, Result, Status, MiniZincError
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

def minizinc_solve_time(result: Result):
    initTime = result.statistics["initTime"].total_seconds() if hasattr(result.statistics, "initTime") else result.statistics["flatTime"].total_seconds()
    return (
        result.statistics["solveTime"].total_seconds() + 
        initTime
    )


def get_minizinc_solution(
    result: Result, instance: Instance, sol: Solution
) -> Solution:
    # solutions
    sol.height = result.objective
    # inputs
    sol.circuits = instance.__getitem__("CIRCUITS")
    sol.n_circuits = instance.__getitem__("N")
    sol.width = instance.__getitem__("W")

    if hasattr(result.solution, "coord_x") and hasattr(result.solution, "coord_y"):
        sol.coords = {"x": result.solution.coord_x, "y": result.solution.coord_y}
    elif hasattr(result.solution, "place"):
        var_place = result.solution.place
        positions = result.solution.coords

        coords = {"x": [None] * sol.n_circuits, "y": [None] * sol.n_circuits}

        for i in range(len(var_place)):
            nc = var_place[i]
            for j in range(len(nc)):
                if nc[j] == 1:
                    coords["x"][i] = round(positions[j] % sol.width)
                    coords["y"][i] = round(positions[j] // sol.width)
        sol.coords = coords

    sol.rotation = None if not hasattr(result.solution, "rot") else result.solution.rot

    # sol.solve_time = ex_time
    # compute_solve_time(ex_time)
    return sol


def run_minizinc(
    input_name: str,
    run_type: RunType,
    model_type: ModelType = ModelType.BASE,
    solver: SolverMinizinc = SolverMinizinc.GECODE,
    timeout: int = None,
    free_search=False,
    height=None
) -> Solution:
    data_file = format_data_file(input_name, InputMode.DZN)
    model_file = format_model_file(run_type, model_type)

    if height is not None:
        model = Model()
        model.add_string(f"int: l_bound = {height};")
        model.add_file(model_file)
    else:
        model = Model(model_file)
    
    solver_exec = Solver.lookup(solver.value)
    instance = Instance(solver_exec, model)

    instance.add_file(data_file, parse_data=True)
    if timeout:
        td_timeout = timedelta(seconds=timeout)
    else:
        td_timeout = None

    try:
        result = instance.solve(timeout=td_timeout, free_search=free_search)
    except MiniZincError as e:
        print(e)
        sol = Solution()
        sol.input_name = input_name
        sol.status = StatusEnum.ERROR
        return sol
        
    # After the instance has been solved
    sol = Solution()
    sol.input_name = input_name
    sol.solve_time = minizinc_solve_time(result)

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
