from enum import Enum
from typing import TypedDict, List


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
    CPLEX: str = "CPLEX_PY"
    MOSEK: str = "MOSEK"
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
    OPTIMAL: int = 1
    NO_SOLUTION: int = -1
    ERROR: int = 0


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
    height: int
    solve_time: str
    n_circuits: int
    circuits: List[List[int]]
    rotation: List[bool]
    coords: Coords
