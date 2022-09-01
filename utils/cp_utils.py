import argparse

from utils.types import DEFAULT_TIMEOUT, ModelType, SolverMinizinc


def parse_cp_argument():
    parser = argparse.ArgumentParser(description="CP solver for VLSI")
    parser.add_argument("instance")
    parser.add_argument("-m", "--model", default=ModelType.BASE, choices=[e.value for e in ModelType])
    parser.add_argument("-s", "--solver", default=SolverMinizinc.GECODE, choices=[e.value for e in SolverMinizinc])
    parser.add_argument("-f", "--freesearch", action="store_true", default=False)
    parser.add_argument("-t", "--timeout", default=DEFAULT_TIMEOUT, type=int)
    parser.add_argument("-v", "--verbose", action="store_true", default=False)
    # TODO merge statistics with instance using append or something similiar
    parser.add_argument("-st", "--statistics", action="store_true", default=False)

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