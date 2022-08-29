from utils.types import Solution, StatusEnum

NO_SOLUTION = "No solution has been found"


def print_logging(solution: Solution):
    if solution.status == StatusEnum.NO_SOLUTION:
        print(NO_SOLUTION)
    else:
        print(
            f"Solving {solution.input_name} with W={solution.width} and H={solution.height}"
        )
        print(f"Time: {solution.solve_time}")

        for i in range(0, solution.n_circuits):
            print(
                (
                    f"{solution.circuits[i][1] if solution.rotation and solution.rotation[i] else solution.circuits[i][0]} {solution.circuits[i][0] if solution.rotation and solution.rotation[i] else solution.circuits[i][1]}, "
                    f"{solution.coords['x'][i]} {solution.coords['y'][i]}"
                )
            )
