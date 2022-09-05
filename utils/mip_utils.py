import argparse
import itertools
from typing import List
import pulp
import mosek

from utils.types import DEFAULT_TIMEOUT, ModelType, Solution, SolverMIP

def build_mip_solution(prob: pulp.LpProblem, sol: Solution, N: int, model_type: ModelType):
    sol.height = round(pulp.value(prob.objective))
    rotation = [False] * N
    coords = {"x": [None] * N, "y": [None] * N}
    for v in prob.variables():
        # print(f"{v.name}: {v.value()}")
        if str(v.name).startswith("coord_x"):
            coords["x"][int(v.name[8:])] = round(v.varValue)
        elif str(v.name).startswith("coord_y"):
            coords["y"][int(v.name[8:])] = round(v.varValue)
        elif str(v.name).startswith("rot"):
            rotation[int(v.name[4:])] = bool(round(v.varValue))

    sol.coords = coords
    sol.rotation = rotation if model_type == ModelType.ROTATION else None
    return sol

def parse_mip_argument():
    parser = argparse.ArgumentParser(description="MIP solver for VLSI")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("-ins", "--instance", help="The name of the instance file without extension (i.e. ins-1 and not ins-1.dzn)")
    parser.add_argument(
        "-m", "--model", default=ModelType.BASE, choices=[e.value for e in ModelType]
    )
    parser.add_argument(
        "-s", "--solver", default=SolverMIP.CPLEX, choices=[e.value for e in SolverMIP]
    )
    parser.add_argument("-t", "--timeout", default=DEFAULT_TIMEOUT, type=int)
    parser.add_argument("-v", "--verbose", action="store_true", default=False)
    # TODO merge statistics with instance using append or something similiar
    mode.add_argument("-test", "--testing", type=int, nargs=2, help="Specify the interval of instances to run the solver on.")
    # parser.add_argument("-st", "--statistics", action="store_true", default=False)

    args = parser.parse_args()
    return vars(args)


def check_mip_solver_exists(solver: SolverMIP):
    if solver == SolverMIP.CPLEX:
        return "CPLEX_CMD" in pulp.listSolvers(onlyAvailable=True)
    elif solver == SolverMIP.MOSEK:
        return "MOSEK" in pulp.listSolvers(onlyAvailable=True)
    elif solver == SolverMIP.MINIZINC:
        # TODO WIP
        return True
    else:
        return False


def check_mip_admissable_timeout(timeout: int):
    return timeout >= 0 and timeout <= (DEFAULT_TIMEOUT * 3 + 1)


def configure_cplex_solver(timeout: int, configuration: List[str] = None):
    solver_verbose = False

    # FIXME remove log for parallel computing
    # https://www.ibm.com/docs/en/icos/22.1.0?topic=cplex-list-parameters
    if configuration is not None:
        # default to True
        warmStart = configuration[0] if isinstance(configuration[0], bool) else False
        options = (
            list(configuration[1:])
            if isinstance(configuration[0], bool) and len(configuration) > 1
            else list(configuration[0:])
        )
        print(f"warmStart: {warmStart} - {options}")
    else:
        # options = []
        options = ["set preprocessing symmetry 5"]

    return pulp.CPLEX_CMD(
        mip=True,
        msg=solver_verbose,
        timeLimit=timeout,
        options=options
    )


def configure_mosek_solver(timeout: int):
    solver_verbose = False

    # https://docs.mosek.com/latest/opt-server/param-groups.html
    options = {
        mosek.dparam.mio_max_time: timeout
    }
    return pulp.MOSEK(mip=True, msg=solver_verbose, options=options)


def create_configuration_dict():
    repeated_tests = 1
    supported_conf = [
        [False],
        ["set preprocessing symmetry " + str(i) for i in [2, 5]]
    ]

    basic_conf = list(itertools.product(*supported_conf))
    set_conf = list(
        itertools.chain.from_iterable(
            itertools.repeat(x, repeated_tests) for x in basic_conf
        )
    )
    return set_conf
