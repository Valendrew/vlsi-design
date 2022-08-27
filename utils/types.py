from enum import Enum

class ModelEnum(Enum):
    BASE: str = "base"
    ROTATION: str = "rotation"

class SolverEnum(Enum):
    GECODE: str = "gecode"
    CHUFFED: str = "chuffed"

class LogicSMT(Enum):
    LIA: str = "LIA"
    QF_IDL: str = "QF_IDL"

class SolverSMT(Enum):
    Z3: str = "z3"
    CVC4: str = "cvc4"