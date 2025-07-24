import mlir.ir as ir
import mlir.dialects.stablehlo as stablehlo
import stablehlo_solver.op_visitor as op_visitor
import z3
from mlir.ir import Type
from mlir.passmanager import PassManager
from typing import Dict, Optional
from enum import Enum, auto


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
        self.init_handlels = {
            ir.IntegerType: self._handle_integer_type,
            ir.F16Type: self._handle_float_type,
            ir.F32Type: self._handle_float_type,
        }
        self._init_hyperparameters(**kwargs)
        self._initialize_arguments()
        self.visitor = op_visitor.OpVisitor(self.solver, self.ref_dict, **kwargs)

    def _init_hyperparameters(self, **kwargs):
        self.negative_fp_min_val = kwargs.get("negative_fp_min_val")
        self.negative_fp_max_val = kwargs.get("negative_fp_max_val")
        self.positive_fp_min_val = kwargs.get("positive_fp_min_val")
        self.positive_fp_max_val = kwargs.get("positive_fp_max_val")
        self.negative_int_min_val = kwargs.get("negative_int_min_val")
        self.positive_int_max_val = kwargs.get("positive_int_max_val")

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

    def _handle_integer_type(self, arg, element_type: ir.IntegerType) -> z3.ArithRef:
        """
        Handle integer type variable initialization and constraint setting.
        """
        if element_type.width == 1:
            # Treat 1-bit integers as boolean values
            return z3.Bool(arg.get_name())

        arg_ref = z3.Int(arg.get_name())
        # Add integer range constraints
        self.solver.add(
            z3.And(
                arg_ref >= self.negative_int_min_val,
                arg_ref <= self.positive_int_max_val,
            )
        )
        return arg_ref

    def _handle_float_type(self, arg, element_type: Type) -> z3.ArithRef:
        """Handle floating-point type variable initialization and constraint setting."""
        arg_ref = z3.Real(arg.get_name())
        self.solver.add(
            z3.Or(
                z3.And(
                    arg_ref >= self.negative_fp_min_val,
                    arg_ref <= self.negative_fp_max_val,
                ),
                z3.And(
                    arg_ref >= self.positive_fp_min_val,
                    arg_ref <= self.positive_fp_max_val,
                ),
            )
        )
        return arg_ref

    def _initialize_arguments(self) -> None:
        """Initialize Z3 variables for function arguments."""
        for arg in self.func.arguments:
            assert isinstance(arg.type, ir.ShapedType)
            handler = self.init_handlels.get(type(arg.type.element_type))
            if handler is None:
                raise TypeError(f"Unsupported argument type: {arg.type.element_type}")
            # Initialize the Z3 variable for the argument
            arg_ref = handler(arg, arg.type.element_type)
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
        res = {}

        for arg in self.func.arguments:
            arg_ref = self.ref_dict[arg]
            if arg_ref.sort().kind() == z3.Z3_REAL_SORT:
                res[arg.get_name()] = model[arg_ref].as_decimal(4)
            else:
                res[arg.get_name()] = model[arg_ref]
        return res

    def reset(self) -> None:
        """Reset the solver state."""
        self.solver.reset()
        self.ref_dict.clear()
