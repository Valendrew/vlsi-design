import os
from os.path import join as join_path
from tracemalloc import Statistic

from utils.types import InputMode, ModelType, RunType, StatisticMode

import sys
sys.path.append("./")


#  TODO change run_type as a global config instead as a parameter of the function


def format_data_file(file: str, mode: InputMode):
    return f"./vlsi-instances/{mode.value}-instances/{file}.{mode.value}"


def format_plot_file(
    run_type: RunType, file: str, model_type: ModelType, solver: str = None
):
    if file.endswith(f".{InputMode.DZN.value}") or file.endswith(
        f".{InputMode.TXT.value}"
    ):
        file = file.split(".")[0]

    if solver is not None:
        plot_path = join_path(
            run_type.value, f"out/plots/{model_type.value}/{solver}/{file}"
        )
    else:
        plot_path = join_path(run_type.value, f"out/plots/{model_type.value}/{file}")

    os.makedirs(plot_path.rsplit("/", maxsplit=1)[0], exist_ok=True)
    return plot_path


def format_model_file(run_type: RunType, model_type: ModelType):
    return join_path(run_type.value, f"src/model_{model_type.value}.mzn")


def format_statistic_file(
    run_type: RunType,
    file: str,
    model_type: ModelType,
    stats_ext: StatisticMode = StatisticMode.CSV,
    solver: str = None,
):
    if solver is not None:
        statistic_path = join_path(
            run_type.value,
            f"out/statistics/{model_type.value}/{solver}/{file}.{stats_ext.value}",
        )
    else:
        statistic_path = join_path(
            run_type.value,
            f"out/statistics/{model_type.value}/{file}.{stats_ext.value}",
        )

    os.makedirs(statistic_path.rsplit("/", maxsplit=1)[0], exist_ok=True)
    return statistic_path
