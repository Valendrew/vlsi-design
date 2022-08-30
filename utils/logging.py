from utils.types import Solution, StatusEnum

NO_SOLUTION_MSG = "No solution has been found"
# TODO append specific error
ERROR_MSG = "Error during execution"
NOT_SOLVED_MSG = "Not optimal solution has been found"
OPTIMAL_MSG = "Optimal solution has been found"


def print_logging(solution: Solution):
    if solution.status == StatusEnum.INFEASIBLE:
        print(NO_SOLUTION_MSG)
        return
    elif solution.status == StatusEnum.ERROR:
        print(ERROR_MSG)
        return
    elif solution.status == StatusEnum.NOT_SOLVED:
        print(NOT_SOLVED_MSG)
    elif solution.status == StatusEnum.OPTIMAL:
        print(OPTIMAL_MSG)
    else:
        raise Exception("No status recognized")

    # Printing logging    
    print(
        f"Solving {solution.input_name} with W={solution.width} and H={solution.height}"
    )
    print(f"Time: {solution.solve_time}")

    # FIXME hidden circuit printing for better reading in console, may be added again
    # for i in range(0, solution.n_circuits):
    #     print(
    #         (
    #             f"{solution.circuits[i][1] if solution.rotation and solution.rotation[i] else solution.circuits[i][0]} {solution.circuits[i][0] if solution.rotation and solution.rotation[i] else solution.circuits[i][1]}, "
    #             f"{solution.coords['x'][i]} {solution.coords['y'][i]}"
    #         )
    #     )