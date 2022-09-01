from enum import Enum
from typing import TypedDict, List

DEFAULT_TIMEOUT = 300

class RunType(Enum):
    CP: str = "CP"
    MIP: str = "MIP"
    SMT: str = "SMT"
    SAT: str = "SAT"


class ModelType(Enum):
    BASE: str = "base"
    ROTATION: str = "rotation"


class SolverMinizinc(Enum):
    GECODE: str = "gecode"
    CHUFFED: str = "chuffed"


class SolverMIP(Enum):
    CPLEX: str = "cplex"
    MOSEK: str = "mosek"
    MINIZINC: str = "minizinc"


class LogicSMT(Enum):
    LIA: str = "LIA"
    QF_IDL: str = "QF_IDL"


class SolverSMT(Enum):
    Z3: str = "z3"
    CVC4: str = "cvc4"


class InputMode(Enum):
    DZN: str = "dzn"
    TXT: str = "txt"


class StatusEnum(Enum):
    FEASIBLE = 2
    OPTIMAL = 1
    NO_SOLUTION_FOUND = 0
    INFEASIBLE = -1
    UNBOUNDED = -2
    ERROR = -3


def SOLUTION_ADMISSABLE(x: StatusEnum):
    return x in [StatusEnum.OPTIMAL, StatusEnum.FEASIBLE]


class StatisticMode(Enum):
    JSON: str = "json"
    CSV: str = "csv"


class Coords(TypedDict):
    x: List[int]
    y: List[int]


class Solution:
    status: StatusEnum
    input_name: str
    width: int
    n_circuits: int
    circuits: List[List[int]]
    height: int
    solve_time: str
    rotation: List[bool] = None
    coords: Coords

    
