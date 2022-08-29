from minizinc import Instance, Model, Solver
from os.path import join as join_path
from datetime import timedelta

import sys
sys.path.append("./")

from utils.plot import plot, plot_cmap
from utils.manage_statistics import save_statistics
from utils.types import ModelEnum, SolverEnum

root_path = "./CP"
model_file = {
    "base": join_path(root_path, "src/model.mzn"),
    "rotation": join_path(root_path, "src/model_rotation.mzn"),
}
plot_path = join_path(root_path, "out/plots/{model}/{file}")
statistics_path = join_path(root_path, "out/statistics/{model}/{file}.csv")
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}


def compute_solution(
    model_type: ModelEnum,
    data_filename: str,
    mode="dzn",
    solver: SolverEnum = SolverEnum.GECODE,
    free_search=False,
    timeout=300,
    verbose=False,
    plots=False,
):
    # Define a verbose print in order to print only if "verbose" is true
    vprint = print if verbose else lambda *a, **k: None

    data_file = data_path[mode].format(file=data_filename)
    plot_file = plot_path.format(
        model=model_type.value, file=data_filename.split(".")[0]
    )

    model = Model(model_file[model_type.value])
    solver = Solver.lookup(solver.value)
    instance = Instance(solver, model)
    instance.add_file(data_file, parse_data=True)
    result = instance.solve(timeout=timedelta(seconds=timeout), free_search=free_search)

    if result.status.OPTIMAL_SOLUTION:
        if not hasattr(result, "solution") or (result.solution is None):
            vprint("No solutions found.")
            return -1

        coords = {"x": result.solution.coord_x, "y": result.solution.coord_y}
        height = result.solution.l

        # inputs
        circuits = instance.__getitem__("CIRCUITS")
        n = instance.__getitem__("N")
        width = instance.__getitem__("W")
        rotation = None if not hasattr(result.solution, "rot") else result.solution.rot

        vprint(f"Solving {data_filename} with W={width} and H={height}")
        ex_time = (
            result.statistics["solveTime"].total_seconds()
            + result.statistics["initTime"].total_seconds()
        )

        magnitude = "s"
        if (ex_time) < 0.01:
            ex_time *= 1000
            magnitude = "ms"
        else:
            magnitude = "s"

        vprint(f"Time: {ex_time} {magnitude}")

        for i in range(0, n):
            vprint(
                (
                    f"{circuits[i][1] if rotation and rotation[i] else circuits[i][0]} {circuits[i][0] if rotation and rotation[i] else circuits[i][1]}, "
                    f"{coords['x'][i]} {coords['y'][i]}"
                )
            )
        if plots:
            plot_cmap(
                width, height, n, circuits, coords, plot_file, rotation, "turbo_r"
            )
        return result


# Compute the solution for the desired number of instances and with the desired solver
def compute_test(
    solver: SolverEnum = SolverEnum.GECODE,
    model_type: ModelEnum = ModelEnum.BASE,
    free_search=False,
    timeout=300,
    verbose=False,
    test_instances=(1, 40),
    save_stats=False,
    plots=False,
):
    stat_format = (
        solver.value
        + "_"
        + str(test_instances[0])
        + "-"
        + str(test_instances[len(test_instances) - 1])
    )
    if isinstance(test_instances, tuple):
        test_iterator = range(test_instances[0], test_instances[1] + 1)
    elif isinstance(test_instances, list):
        stat_format += "_uncontinguous"
        test_iterator = test_instances
    else:
        return

    statistics_file = statistics_path.format(model=model_type.value, file=stat_format)

    for i in test_iterator:
        result = compute_solution(
            model_type,
            f"ins-{i}.dzn",
            solver=solver,
            free_search=free_search,
            timeout=timeout,
            verbose=verbose,
            plots=plots
        )
        print(f"- Computed a solution for instance {i}.")
        if save_stats:
            save_statistics(statistics_file, result, i)


if __name__ == "__main__":
    compute_solution(
        ModelEnum.BASE,
        "ins-5.dzn",
        solver=SolverEnum.CHUFFED,
        free_search=True,
        plots=True,
        verbose=True,
    )
    """ compute_test(
        SolverEnum.CHUFFED,
        model_type=ModelEnum.ROTATION,
        free_search=True,
        timeout=300,
        verbose=False,
        test_instances=[1, 2, 3, 4, 5, 15],
        save_stats=True,
        plots=True,
    ) """
