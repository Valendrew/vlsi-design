from enum import Enum

class ModelEnum(Enum):
    BASE: str = "base"
    ROTATION: str = "rotation"

class SolverEnum(Enum):
    GECODE: str = "gecode"
    CHUFFED: str = "chuffed"