from utils.types import SOLUTION_ADMISSABLE, Solution, StatusEnum

FEASIBLE_MSG = "A solution has been found, but not an optimal one"
OPTIMAL_MSG = "Optimal solution has been found"
NO_SOLUTION_MSG = "No solution has been found"
GENERIC_MSG = "Infeasible solution"
# TODO append specific error
ERROR_MSG = "Error during execution"


def print_logging(solution: Solution):
    if solution.status == StatusEnum.FEASIBLE:
        print(FEASIBLE_MSG)
    elif solution.status == StatusEnum.OPTIMAL:
        print(OPTIMAL_MSG)
    elif solution.status == StatusEnum.NO_SOLUTION_FOUND:
        print(NO_SOLUTION_MSG)
    elif solution.status == StatusEnum.ERROR:
        print(ERROR_MSG)
    else:
        print(GENERIC_MSG)

    if SOLUTION_ADMISSABLE(solution.status):
        # Printing logging
        print(
            f"Solved {solution.input_name} with W={solution.width} and H={solution.height}"
        )
        print(f"Time: {solution.solve_time}")

        for i in range(0, solution.n_circuits):
            print(
                (
                    f"{solution.circuits[i][1] if solution.rotation and solution.rotation[i] else solution.circuits[i][0]} {solution.circuits[i][0] if solution.rotation and solution.rotation[i] else solution.circuits[i][1]}, "
                    f"{solution.coords['x'][i]} {solution.coords['y'][i]}"
                )
            )
