from minizinc import Instance, Model, Solver
from os.path import join as join_path
from datetime import timedelta

from utils.plot import plot, plot_cmap
from utils.manage_statistics import save_statistics

root_path = "./CP"
model_file = join_path(root_path, "src/model.mzn")
plot_path = join_path(root_path, "out/plots/{file}")
statistics_path = join_path(root_path, "out/statistics/{file}.csv")
data_path = {
    "dzn": "./vlsi-instances/dzn-instances/{file}",
    "txt": "./vlsi-instances/txt-instances/{file}",
}


def compute_solution(data_filename: str, mode="dzn", solver="gecode", free_search=False, timeout=300, verbose=False, plots=False):
    # Define a verbose print in order to print only if "verbose" is true
    vprint = print if verbose else lambda *a, **k: None

    data_file = data_path[mode].format(file=data_filename)
    plot_file = plot_path.format(file=data_filename.split(".")[0])

    model = Model(model_file)
    solver = Solver.lookup(solver)
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

        vprint(f"Solving {data_filename} with W={width} and H={height}")
        ex_time = result.statistics['solveTime'].total_seconds() + result.statistics['initTime'].total_seconds()

        magnitude = "s"
        if (ex_time) < 0.01:
            ex_time *= 1000
            magnitude = "ms"
        else:
            magnitude = "s"

        vprint(f"Time: {ex_time} {magnitude}")

        for i in range(0, n):
            vprint(
                f"{circuits[i][0]} {circuits[i][1]}, {coords['x'][i]} {coords['y'][i]}"
            )
        if plots:
            plot_cmap(width, height, n, circuits, coords, plot_file, "turbo_r")
        return result


# Compute the solution for the desired number of instances and with the desired solver
def compute_test(solver="gecode", free_search=False, timeout=300, verbose=False, test_instances=(1,40), save_stats=False):
    statistics_file = statistics_path.format(file=solver+"_"+str(test_instances[0])+"-"+str(test_instances[1]))
    for i in range(test_instances[0], test_instances[1]+1):
        result = compute_solution(f"ins-{i}.dzn", solver=solver, free_search=free_search, timeout=timeout, verbose=verbose)
        print(f"- Computed a solution for instance {i}.")
        if save_stats:
            save_statistics(statistics_file, result, i)


if __name__ == "__main__":
    compute_solution("ins-32.dzn", solver="chuffed", free_search=True, plots=True, verbose=True)
    #compute_test("chuffed", free_search=True, timeout=300, verbose=False, test_instances=(1, 10), save_stats=True)