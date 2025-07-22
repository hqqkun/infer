import mlir.ir as ir
from mlir.ir import Type
from mlir.passmanager import PassManager
import mlir.dialects.stablehlo as stablehlo
from typing import Dict, Optional
import z3
from enum import Enum, auto
import stablehlo_solver.op_visitor as op_visitor


class SolverStatus(Enum):
    SUCCESS = auto()
    FAILURE = auto()


class MLIRSolver:
    """A solver that analyzes MLIR models using Z3 constraints."""

    def __init__(self, model_str: str, **kwargs) -> None:
        """Initialize the solver with MLIR model string."""
        self.satisfiable = None
        # Assuming timeout is provided in seconds.
        z3.set_param(
            "timeout", kwargs.get("timeout") * 1000
        )  # Set timeout in milliseconds
        self.solver = z3.Solver()
        self.module = self._parse_and_optimize_module(model_str)
        self.func = self._get_entry_function()
        self.ref_dict: Dict[ir.Value, z3.ArithRef] = {}
        self._init_hyperparameters(**kwargs)
        self._initialize_arguments()
        self.visitor = op_visitor.OpVisitor(self.solver, self.ref_dict, **kwargs)

    def _init_hyperparameters(self, **kwargs):
        self.negative_min_val = kwargs.get("negative_min_val")
        self.negative_max_val = kwargs.get("negative_max_val")
        self.positive_min_val = kwargs.get("positive_min_val")
        self.positive_max_val = kwargs.get("positive_max_val")

    def _parse_and_optimize_module(self, model_str: str) -> ir.Module:
        """Parse MLIR and apply optimization passes."""
        with ir.Context() as ctx:
            stablehlo.register_dialect(ctx)
            stablehlo.register_stablehlo_passes()

            pm = PassManager.parse(
                "builtin.module("
                "  cse, canonicalize, stablehlo-refine-shapes,"
                "  func.func(stablehlo-canonicalize-dynamism)"
                ")"
            )
            module = ir.Module.parse(model_str)
            pm.run(module.operation)
            return module

    def _get_entry_function(self) -> ir.Operation:
        """Get the first function in the module."""
        if not self.module.body.operations:
            raise ValueError("Empty module")
        return self.module.body.operations[0]

    def _initialize_input_value_range(
        self, value: Optional[z3.ArithRef], element_type: Type
    ) -> None:
        """Initialize the range constraints for input values."""
        if value is None:
            return

        if isinstance(element_type, ir.IntegerType) and element_type.width == 1:
            # For boolean types, we can use a simple constraint
            self.solver.add(z3.Or(value == 0, value == 1))
        else:
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
            assert isinstance(arg.type, ir.ShapedType)
            self._initialize_input_value_range(arg_ref, arg.type.element_type)
            self.ref_dict[arg] = arg_ref

    def analyze(self) -> SolverStatus:
        """Run the full analysis pipeline."""
        for op in self.func.body.blocks[0].operations:
            if self.visitor.visit_op(op) == op_visitor.Status.FAILURE:
                print(f"Operation processing failed: {op}")
                return SolverStatus.FAILURE

        print("All operations visited successfully.")
        return SolverStatus.SUCCESS

    @property
    def is_satisfiable(self) -> bool:
        """Check if constraints are satisfiable."""
        if self.satisfiable is None:
            print("Checking satisfiability of constraints...")
            result = self.solver.check()
            if result == z3.unknown:
                print("Solver returned unknown status: ", self.solver.reason_unknown())
            self.satisfiable = result == z3.sat
        return self.satisfiable

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
