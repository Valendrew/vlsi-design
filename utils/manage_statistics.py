import os
from typing import Iterator, List, Union
import pandas as pd

from utils.types import SOLUTION_ADMISSABLE, Solution, StatusEnum


# Save useful statistics in a csv file
# TODO: implement a mechanism in order to avoid always appending at the end of the file with the same name
def save_statistics(statistic_path: str, solution: Solution):
    # columns = ["instance", "l", "coord_x", "coord_y", "nodes", "failures", "restarts", "variables", "propagations", "solveTime", "nSolutions"]
    columns = [
        "input_name",
        "status",
        "height",
        "solve_time",
        "rotation",
        "coords_x",
        "coords_y",
    ]
    if os.path.exists(statistic_path):
        df = pd.read_csv(statistic_path)
    else:
        df = pd.DataFrame(columns=columns)

    sol_vars = vars(solution).copy()
    sol_vars["status"] = StatusEnum(sol_vars["status"]).name
    if SOLUTION_ADMISSABLE(solution.status):
        values = [
            sol_vars[c.split("_")[0]][c.split("_")[1]]
            if c in ["coords_x", "coords_y"]
            else sol_vars[c]
            for c in columns
        ]
    else:
        values = [sol_vars[c] if c in ["input_name", "status"] else None for c in columns]
    values = [[v] if isinstance(v, list) else v for v in values]

    df = pd.concat([df, pd.DataFrame(dict(zip(columns, values)), index=[0])], ignore_index=True)
    df.to_csv(statistic_path, index=False)


def checking_instances(instances_list) -> Union[List[int], Iterator[int]]:
    # If instances must be treated as a range
    if isinstance(instances_list, tuple):
        return range(instances_list[0], instances_list[1] + 1)
    # If explicits instances are passed as a list
    elif isinstance(instances_list, list):
        return instances_list
    else:
        raise TypeError("Statistic instances must be of type list or tuple")
