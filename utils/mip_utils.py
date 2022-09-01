import argparse
import pulp
import mosek

from utils.types import DEFAULT_TIMEOUT, ModelType, SolverMIP


def parse_mip_argument():
    parser = argparse.ArgumentParser(description="MIP solver for VLSI")
    parser.add_argument("instance")
    parser.add_argument(
        "-m", "--model", default=ModelType.BASE, choices=[e.value for e in ModelType]
    )
    parser.add_argument(
        "-s", "--solver", default=SolverMIP.CPLEX, choices=[e.value for e in SolverMIP]
    )
    parser.add_argument("-t", "--timeout", default=DEFAULT_TIMEOUT, type=int)
    parser.add_argument("-v", "--verbose", action="store_true", default=False)
    # TODO merge statistics with instance using append or something similiar
    parser.add_argument("-st", "--statistics", action="store_true", default=False)

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


def configure_cplex_solver(timeout: int):
    solver_verbose = False

    return pulp.CPLEX_CMD(
        mip=True,
        msg=solver_verbose,
        timeLimit=timeout,
        options=["set preprocessing symmetry 5"],
        warmStart=True,
    )


def configure_mosek_solver(timeout: int):
    solver_verbose = False

    # https://docs.mosek.com/latest/opt-server/param-groups.html
    options = {
        # mosek.iparam.num_threads: 8,
        mosek.dparam.mio_max_time: timeout,
        mosek.iparam.mio_symmetry_level: 4,
        mosek.iparam.optimizer: "MSK_OPTIMIZER_PRIMAL_SIMPLEX",
    }
    return pulp.MOSEK(mip=True, msg=solver_verbose, options=options)
