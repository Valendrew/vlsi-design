import argparse
from utils.types import DEFAULT_TIMEOUT, ModelType, SolverMinizinc


def parse_cp_argument():
    parser = argparse.ArgumentParser(description="CP solver for VLSI")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("-ins", "--instance", help="The name of the instance file without extension (i.e. ins-1 and not ins-1.dzn)")
    parser.add_argument("-m", "--model", default=ModelType.BASE, choices=[e.value for e in ModelType])
    parser.add_argument("-s", "--solver", default=SolverMinizinc.GECODE, choices=[e.value for e in SolverMinizinc])
    parser.add_argument("-f", "--freesearch", action="store_true", default=False)
    parser.add_argument("-t", "--timeout", default=DEFAULT_TIMEOUT, type=int)
    parser.add_argument("-v", "--verbose", action="store_true", default=False)
    mode.add_argument("-test", "--testing", type=int, nargs=2, help="Specify the interval of instances to run the solver on.")

    args = parser.parse_args()
    return vars(args)


def check_cp_solver_exists(solver: SolverMinizinc):
    if solver == SolverMinizinc.CHUFFED:
        return True
    elif solver == SolverMinizinc.GECODE:
        return True
    else:
        return False


def check_cp_admissable_timeout(timeout: int):
    return timeout >= 0 and timeout <= (DEFAULT_TIMEOUT * 3 + 1)