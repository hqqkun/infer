import z3
import mlir.ir as ir
import mlir.dialects.stablehlo as stablehlo
import mlir.dialects.tensor as tensor
import mlir.dialects.arith as arith
import mlir.dialects.shape as shape
from functools import singledispatchmethod
from enum import Enum
from typing import Optional
import math


class Status(Enum):
    FAILURE = 0
    SUCCESS = 1


class OpVisitor:
    def __init__(self, solver: z3.Solver, ref_dict: dict):
        self.solver = solver
        self.ref_dict = ref_dict
        self.f16_min_val = -60000
        self.f16_max_val = 60000
        self.ln_f16_max_val = math.log(self.f16_max_val)

    def set_range_constraints(
        self, value: Optional[z3.ArithRef], min_val: float = None, max_val: float = None
    ):
        if value is None:
            return
        max_bound = max_val if max_val is not None else self.f16_max_val
        min_bound = min_val if min_val is not None else self.f16_min_val
        self.solver.add(value > min_bound, value < max_bound)

    def boolean_range_constraint(self, value: Optional[z3.ArithRef]):
        if value is not None:
            self.solver.add(z3.Or(value == 0, value == 1))

    def get_max_ref(self, lhs: z3.ArithRef, rhs: z3.ArithRef) -> z3.ArithRef:
        return z3.If(lhs > rhs, lhs, rhs)

    def get_min_ref(self, lhs: z3.ArithRef, rhs: z3.ArithRef) -> z3.ArithRef:
        return z3.If(lhs < rhs, lhs, rhs)

    def get_max_dim(self, type: ir.RankedTensorType) -> Optional[z3.ArithRef]:
        """Returns the maximum dimension size as a Z3 Real variable if the shape is static."""
        if type.has_static_shape:
            return z3.RealVal(max(type.shape))
        return None

    def get_max_dynamic_dim(self) -> int:
        """Returns the maximum dynamic dimension size."""
        return 2048

    @singledispatchmethod
    def process_op(self, op):
        return Status.SUCCESS

    @process_op.register(stablehlo.AddOp)
    def _(self, op: stablehlo.AddOp):
        result = self.ref_dict[op.lhs] + self.ref_dict[op.rhs]
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.SubtractOp)
    def _(self, op: stablehlo.SubtractOp):
        result = self.ref_dict[op.lhs] - self.ref_dict[op.rhs]
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.MulOp)
    def _(self, op: stablehlo.MulOp):
        result = self.ref_dict[op.lhs] * self.ref_dict[op.rhs]
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.DivOp)
    def _(self, op: stablehlo.DivOp):
        rhs = self.ref_dict[op.rhs]
        self.solver.add(rhs != 0)
        result = self.ref_dict[op.lhs] / rhs
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.MaxOp)
    def _(self, op: stablehlo.MaxOp):
        result = self.get_max_ref(self.ref_dict[op.lhs], self.ref_dict[op.rhs])
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.MinOp)
    def _(self, op: stablehlo.MinOp):
        result = self.get_min_ref(self.ref_dict[op.lhs], self.ref_dict[op.rhs])
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.ConstantOp)
    def _(self, op: stablehlo.ConstantOp):
        splat_value = op.value.get_splat_value().value
        if splat_value == float("nan"):
            return Status.FAILURE  # NaN is not a valid value in this context

        result_value = None
        if splat_value == float("+inf"):
            result_value = z3.RealVal(self.f16_max_val)
        elif splat_value == float("-inf"):
            result_value = z3.RealVal(self.f16_min_val)
        else:
            result_value = z3.RealVal(float(splat_value))
        self.ref_dict[op.output] = result_value
        return Status.SUCCESS

    @process_op.register(stablehlo.DotOp)
    def _(self, op: stablehlo.DotOp):
        lhs_type = op.lhs.type
        assert isinstance(lhs_type, ir.RankedTensorType)
        if lhs_type.is_dynamic_dim(1):
            return Status.FAILURE  # Cannot process dynamic dimensions
        result = (
            self.ref_dict[op.lhs]
            * self.ref_dict[op.rhs]
            * z3.RealVal(lhs_type.shape[1])
        )
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.DotGeneralOp)
    def _(self, op: stablehlo.DotGeneralOp):
        lhs_type = op.lhs.type
        assert isinstance(lhs_type, ir.RankedTensorType)
        dot_dims_attr = stablehlo.DotDimensionNumbers(op.dot_dimension_numbers)
        result = self.ref_dict[op.lhs] * self.ref_dict[op.rhs]
        for dim in dot_dims_attr.lhs_contracting_dimensions:
            if lhs_type.is_dynamic_dim(dim):
                result *= z3.RealVal(self.get_max_dynamic_dim())
            else:
                result *= z3.RealVal(lhs_type.shape[dim])
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.RsqrtOp)
    def _(self, op: stablehlo.RsqrtOp):
        operand = self.ref_dict[op.operand]
        result = 1 / z3.Sqrt(operand)
        self.set_range_constraints(result, min_val=0.0)
        self.set_range_constraints(operand, min_val=0.0)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.NegOp)
    def _(self, op: stablehlo.NegOp):
        result = -self.ref_dict[op.operand]
        # TODO: Should we add a range constraint here?
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.ExpOp)
    def _(self, op: stablehlo.ExpOp):
        operand = self.ref_dict[op.operand]
        # For simplicity, we just ensure the operand is within a reasonable range.
        self.solver.add(operand <= self.ln_f16_max_val)
        result = z3.Real(op.result.get_name())
        self.ref_dict[op.result] = result
        self.set_range_constraints(result, min_val=0.0, max_val=self.f16_max_val)
        return Status.SUCCESS

    @process_op.register(stablehlo.CompareOp)
    def _(self, op: stablehlo.CompareOp):
        result = z3.Real(op.result.get_name())
        # Just set zero or one.
        self.solver.add(z3.Or(result == 0, result == 1))
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.ConcatenateOp)
    def _(self, op: stablehlo.ConcatenateOp):
        operands = [self.ref_dict[operand] for operand in op.inputs]
        # Return the maximum.
        value = operands[0]
        for operand in operands[1:]:
            value = self.get_max_ref(value, operand)
        self.set_range_constraints(value)
        self.ref_dict[op.result] = value
        return Status.SUCCESS

    @process_op.register(stablehlo.ReduceOp)
    def _(self, op: stablehlo.ReduceOp):
        src = op.inputs[0]
        src_type = src.type
        assert isinstance(src_type, ir.RankedTensorType)
        apply_op = op.body.blocks[0].operations[0]
        if isinstance(apply_op, stablehlo.AddOp):
            numel = 1
            for dim in op.dimensions:
                if src_type.is_dynamic_dim(dim):
                    numel = self.get_max_dynamic_dim()
                else:
                    numel *= src_type.shape[dim]
            result = self.ref_dict[src] * z3.RealVal(numel)
            self.set_range_constraints(result)
            self.ref_dict[op.result] = result
        elif isinstance(apply_op, stablehlo.MaxOp):
            self.ref_dict[op.result] = self.ref_dict[src]
        else:
            return Status.FAILURE
        return Status.SUCCESS

    @process_op.register(stablehlo.SignOp)
    def _(self, op: stablehlo.SignOp):
        operand = self.ref_dict[op.operand]
        result = z3.If(operand > 0, 1, z3.If(operand < 0, -1, 0))
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.SelectOp)
    def _(self, op: stablehlo.SelectOp):
        condition = self.ref_dict[op.pred]
        true_value = self.ref_dict[op.on_true]
        false_value = self.ref_dict[op.on_false]
        # TODO: Make more precise with ranges.
        result = z3.If(condition == 1, true_value, false_value)
        self.solver.add(
            z3.Or(condition == 0, condition == 1)
        )  # Ensure condition is boolean
        self.set_range_constraints(result)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.AndOp)
    @process_op.register(stablehlo.OrOp)
    @process_op.register(stablehlo.XorOp)
    def _(self, op):
        # These operations are boolean, so we just ensure the result is 0 or 1.
        result = z3.Real(op.result.get_name())
        self.solver.add(z3.Or(result == 0, result == 1))
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.NotOp)
    def _(self, op: stablehlo.NotOp):
        # Not operation flips the boolean value
        operand = self.ref_dict[op.operand]
        result = z3.If(operand == 0, 1, 0)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.LogisticOp)
    def _(self, op: stablehlo.LogisticOp):
        # Logistic function: 1 / (1 + exp(-x))
        # However, for simplicity, we just ensure the result is within a reasonable range.
        result = z3.Real(op.result.get_name())
        self.set_range_constraints(result, min_val=0.0, max_val=1.0)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.TanhOp)
    def _(self, op: stablehlo.TanhOp):
        # Tanh function: (exp(x) - exp(-x)) / (exp(x) + exp(-x))
        # For simplicity, we just ensure the result is within a reasonable range.
        result = z3.Real(op.result.get_name())
        self.set_range_constraints(result, min_val=-1.0, max_val=1.0)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.Log1pOp)
    def _(self, op: stablehlo.Log1pOp):
        operand = self.ref_dict[op.operand]
        # Log1p(x) = log(1 + x)
        # We ensure the operand is greater than -1 to avoid log(0).
        self.solver.add(operand > -1.0)
        result = z3.Real(op.result.get_name())
        self.set_range_constraints(result, max_val=self.ln_f16_max_val)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.BroadcastInDimOp)
    @process_op.register(stablehlo.ConvertOp)
    @process_op.register(stablehlo.DynamicBroadcastInDimOp)
    @process_op.register(stablehlo.DynamicPadOp)
    @process_op.register(stablehlo.DynamicReshapeOp)
    @process_op.register(stablehlo.DynamicSliceOp)
    @process_op.register(stablehlo.GatherOp)
    @process_op.register(stablehlo.PadOp)
    @process_op.register(stablehlo.RealDynamicSliceOp)
    @process_op.register(stablehlo.ReshapeOp)
    @process_op.register(stablehlo.SliceOp)
    @process_op.register(stablehlo.TorchIndexSelectOp)
    @process_op.register(stablehlo.TransposeOp)
    def _(self, op):
        # These operations do not change the values, just the shape
        self.ref_dict[op.result] = self.ref_dict[op.operand]
        return Status.SUCCESS

    @process_op.register(tensor.ExpandShapeOp)
    @process_op.register(tensor.CollapseShapeOp)
    def _(self, op):
        # These operations change the shape but not the value
        self.ref_dict[op.result] = self.ref_dict[op.src]
        return Status.SUCCESS

    @process_op.register(tensor.ExtractSliceOp)
    def _(self, op: tensor.ExtractSliceOp):
        self.ref_dict[op.result] = self.ref_dict[op.source]
        return Status.SUCCESS

    @process_op.register(tensor.DimOp)
    def _(self, op: tensor.DimOp):
        # DimOp returns the size of a dimension
        source_type = op.source.type
        index_opview = op.index.owner.opview
        #TODO: Handle this

        dim_index = op.dimension.value
        if source_type.is_dynamic_dim(dim_index):
            result = z3.Real(op.result.get_name())
            self.set_range_constraints(
                result, min_val=0, max_val=self.get_max_dynamic_dim()
            )
        else:
            result = z3.RealVal(source_type.shape[dim_index])
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(arith.IndexCastOp)
    def _(self, op: arith.IndexCastOp):
        # IndexCastOp converts an index type to another index type
        self.ref_dict[op.result] = self.ref_dict[op.in_]
        return Status.SUCCESS

    @process_op.register(shape.ShapeOfOp)
    def _(self, op: shape.ShapeOfOp):
        arg_type = op.arg.type
        assert isinstance(arg_type, ir.RankedTensorType)
        opt_max_dim = self.get_max_dim(arg_type)
        if opt_max_dim is not None:
            self.ref_dict[op.result] = opt_max_dim
        else:
            result = z3.Real(op.result.get_name())
            self.set_range_constraints(
                result, min_val=0, max_val=self.get_max_dynamic_dim()
            )
            self.ref_dict[op.result] = result
        return Status.SUCCESS

    def visit_op(self, op: ir.Operation):
        """
        Visit an operation and process it based on its type.
        """
        try:
            return self.process_op(op)
        except Exception as e:
            raise e
