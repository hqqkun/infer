import mlir.ir as ir
from mlir.passmanager import PassManager
import mlir.dialects.stablehlo as stablehlo
from typing import Dict, Optional
import z3
from enum import Enum, auto
import op_visitor


class SolverStatus(Enum):
    SUCCESS = auto()
    FAILURE = auto()


class MLIRSolver:
    """A solver that analyzes MLIR models using Z3 constraints."""

    def __init__(self, model_str: str) -> None:
        """Initialize the solver with MLIR model string."""
        self.solver = z3.Solver()
        self.module = self._parse_and_optimize_module(model_str)
        self.func = self._get_entry_function()
        self.ref_dict: Dict[ir.Value, z3.ArithRef] = {}
        self.negative_min_val = -10.0
        self.negative_max_val = -0.01
        self.positive_min_val = 0.01
        self.positive_max_val = 10.0

    def _parse_and_optimize_module(self, model_str: str) -> ir.Module:
        """Parse MLIR and apply optimization passes."""
        with ir.Context() as ctx:
            stablehlo.register_dialect(ctx)
            stablehlo.register_stablehlo_passes()

            # pm = PassManager.parse(
            #     "builtin.module("
            #     "  cse, canonicalize, stablehlo-refine-shapes,"
            #     "  func.func(stablehlo-canonicalize-dynamism)"
            #     ")"
            # )
            module = ir.Module.parse(model_str)
            # pm.run(module.operation)
            return module

    def _get_entry_function(self) -> ir.Operation:
        """Get the first function in the module."""
        if not self.module.body.operations:
            raise ValueError("Empty module")
        return self.module.body.operations[0]

    def _initialize_input_value_range(self, value: Optional[z3.ArithRef]) -> None:
        """Initialize the range constraints for input values."""
        if value is not None:
            self.solver.add(
                z3.Or(
                    z3.And(
                        value >= self.negative_min_val, value <= self.negative_max_val
                    ),
                    z3.And(
                        value >= self.positive_min_val, value <= self.positive_max_val
                    ),
                )
            )

    def _initialize_arguments(self) -> None:
        """Initialize Z3 variables for function arguments."""
        for arg in self.func.arguments:
            arg_ref = z3.Real(arg.get_name())
            self._initialize_input_value_range(arg_ref)
            self.ref_dict[arg] = arg_ref

    def analyze(self) -> SolverStatus:
        """Run the full analysis pipeline."""
        self._initialize_arguments()

        visitor = op_visitor.OpVisitor(self.solver, self.ref_dict)
        for op in self.func.body.blocks[0].operations:
            if visitor.visit_op(op) == op_visitor.Status.FAILURE:
                print(f"Operation processing failed: {op}")
                return SolverStatus.FAILURE

        return SolverStatus.SUCCESS

    @property
    def is_satisfiable(self) -> bool:
        """Check if constraints are satisfiable."""
        return self.solver.check() == z3.sat

    def get_model(self) -> Dict[str, z3.ExprRef]:
        """Get the solved model values."""
        if not self.is_satisfiable:
            raise RuntimeError("Model is not satisfiable")

        model = self.solver.model()
        return {
            arg.get_name(): model[self.ref_dict[arg]] for arg in self.func.arguments
        }

    def reset(self) -> None:
        """Reset the solver state."""
        self.solver.reset()
        self.ref_dict.clear()
