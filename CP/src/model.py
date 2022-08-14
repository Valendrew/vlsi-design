from minizinc import Instance, Model, Solver
from os.path import join as join_path
from datetime import timedelta

from plot import plot, plot_cmap

root_path = "./CP"
model_file = join_path(root_path, "src/model.mzn")
plot_path = join_path(root_path, "out/{file}")
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}


def compute_solution(data_filename: str, mode="dzn"):
    data_file = data_path[mode].format(file=data_filename)
    plot_file = plot_path.format(file=data_filename.split(".")[0])

    model = Model(model_file)
    solver = Solver.lookup("gecode")
    instance = Instance(solver, model)
    instance.add_file(data_file, parse_data=True)
    result = instance.solve(timeout=timedelta(seconds=30))

    if result.status.OPTIMAL_SOLUTION:
        if not hasattr(result, "solution") or (result.solution is None):
            print("No solutions found within the time limits.")
            return -1

        coords = {"x": result.solution.coord_x, "y": result.solution.coord_y}
        height = result.solution.l

        # inputs
        circuits = instance.__getitem__("CIRCUITS")
        n = instance.__getitem__("N")
        width = instance.__getitem__("W")

        print(f"Solving {data_filename} with W={width} and H={height}")
        ex_time = result.statistics['solveTime'].total_seconds()
        magnitude = "s"

        if (ex_time) < 0.01:
            ex_time *= 1000
            magnitude = "ms"
        else:
            magnitude = "s"

        print(f"Time: {ex_time} {magnitude}")

        for i in range(0, n):
            print(
                f"{circuits[i][0]} {circuits[i][1]}, {coords['x'][i]} {coords['y'][i]}"
            )
        plot_cmap(width, height, n, circuits, coords, plot_file, "turbo_r")


if __name__ == "__main__":
    compute_solution("ins-14.dzn")