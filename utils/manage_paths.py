import sys
sys.path.append("./")

from glob import glob
from os import makedirs
from os.path import join as join_path, exists
import logging
from re import I
from typing import Iterator, List, Union
from utils.types import InputMode, ModelType, RunType, StatisticMode

def format_data_file(file: str, mode: InputMode):
    file_path = f"./vlsi-instances/{mode.value}-instances/{file}.{mode.value}"
    if exists(file_path):
        return file_path
    else:
        logging.error(f"The file {file_path} doesn't exist, provide a valid one")
        raise FileNotFoundError


def format_plot_file(
    run_type: RunType, file: str, model_type: ModelType, solver: str = None
):
    if file.endswith(f".{InputMode.DZN.value}") or file.endswith(
        f".{InputMode.TXT.value}"
    ):
        file = file.split(".")[0]

    if solver is not None:
        plot_path = join_path(
            run_type.value, f"out/{model_type.value}/{solver}/plots/{file}.png"
        )
    else:
        plot_path = join_path(run_type.value, f"out/{model_type.value}/plots/{file}.png")

    makedirs(plot_path.rsplit("/", maxsplit=1)[0], exist_ok=True)
    return plot_path


def format_model_file(run_type: RunType, model_type: ModelType):
    # return join_path(run_type.value, "src", "model_{model_type.value}.mzn")
    return f"{run_type.value}/src/model_{model_type.value}.mzn"


def format_statistic_file(
    run_type: RunType,
    test_instances: Union[List[int], Iterator[int]],
    model_type: ModelType,
    stats_ext: StatisticMode = StatisticMode.CSV,
    solver: str = None,
):
    if test_instances[0] == test_instances[1]:
        file = f"{test_instances[0]}"
    else:
        file = f"{min(test_instances)}_{max(test_instances)}"
    
    statistic_path = join_path(run_type.value, f"out/{model_type.value}/statistics")

    # Checking if the directory exists
    makedirs(statistic_path, exist_ok=True)

    """ Checking if the basename file already exists, 
    then append the number of occurences in order to have an unique name """
    if solver is not None:
        statistic_path = join_path(statistic_path, f"{solver}_{file}" + "-{suffix}")
    else:
        statistic_path = join_path(statistic_path, f"{file}" + "-{suffix}")

    same_file_len = len(glob(statistic_path.format(suffix="*")))
    return statistic_path.format(suffix=f"{same_file_len}.{stats_ext.value}")
