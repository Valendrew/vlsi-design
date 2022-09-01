import os
import pandas as pd
import numpy as np

from utils.types import Solution, StatusEnum


# Save useful statistics in a csv file
# TODO: implement a mechanism in order to avoid always appending at the end of the file with the same name
def save_statistics(statistic_path: str, solution: Solution):
    # columns = ["instance", "l", "coord_x", "coord_y", "nodes", "failures", "restarts", "variables", "propagations", "solveTime", "nSolutions"]
    columns = ["input_name", "status", "height", "solve_time", "rotation", "coords_x", "coords_y"]
    if os.path.exists(statistic_path):
        df = pd.read_csv(statistic_path)
    else:
        df = pd.DataFrame(columns=columns)

    sol_vars = vars(solution).copy()
    sol_vars["status"] = StatusEnum(sol_vars["status"]).name
    values = [[sol_vars[c.split("_")[0]][c.split("_")[1]]] if c in ["coords_x", "coords_y"] else sol_vars[c] for c in columns ]

    df = pd.concat([df, pd.DataFrame(dict(zip(columns, values)))], ignore_index=True)
    df.to_csv(statistic_path, index=False)