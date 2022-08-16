import os
import pandas as pd


# Save useful statistics in a csv file
# TODO: implement a mechanism in order to avoid always appending at the end of the file with the same name
def save_statistics(stat_file, results):
    columns = ["l", "coord_x", "coord_y", "nodes", "failures", "restarts", "variables", "propagations", "solveTime", "nSolutions"]
    if os.path.exists(stat_file):
        df = pd.read_csv(stat_file)
    else:
        df = pd.DataFrame(columns=columns)

    values = [[getattr(results.solution, col)] if col.startswith("c") else getattr(results.solution, col) for col in columns[:3]]
    for col in columns[3:]:
        if col == "solveTime":
            values.append(results.statistics[col].total_seconds() + results.statistics["initTime"].total_seconds())
        else:
            values.append(results.statistics[col])
    
    df = pd.concat([df, pd.DataFrame(dict(zip(columns, values)))], ignore_index=True)
    df.to_csv(stat_file, index=False)