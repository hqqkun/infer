import math
import mlir.ir as ir
import mlir.dialects.stablehlo as stablehlo
import mlir.dialects.tensor as tensor
import mlir.dialects.arith as arith
import mlir.dialects.shape as shape
import z3
from functools import singledispatchmethod
from enum import Enum
from typing import Optional
from mlir.ir import Type

import logging

logger = logging.getLogger(__name__)


class Status(Enum):
    FAILURE = 0
    SUCCESS = 1


class OpVisitor:
    class RangeConfig:
        def __init__(self, **kwargs):
            self.f16_min_val = kwargs.get("f16_min")
            self.f16_max_val = kwargs.get("f16_max")
            self.f32_min_val = kwargs.get("f32_min")
            self.f32_max_val = kwargs.get("f32_max")
            self.i64_min_val = kwargs.get("i64_min")
            self.i64_max_val = kwargs.get("i64_max")
            self.max_dynamic_dim = kwargs.get("max_dynamic_dim")
            self.ln_f16_max_val = math.log(self.f16_max_val)
            self.ln_f32_max_val = math.log(self.f32_max_val)

    def __init__(self, solver: z3.Solver, ref_dict: dict, **kwargs):
        self.solver = solver
        self.ref_dict = ref_dict
        self.config = self.RangeConfig(**kwargs)
        # %0 = shape.shape_of %arg0 : tensor<?x130x25xf32> -> tensor<3xindex>
        # {%0 : [?, 130, 25]}
        self.association_type_dict = {}

    @property
    def f16_min_val(self):
        return self.config.f16_min_val

    @property
    def f16_max_val(self):
        return self.config.f16_max_val

    @property
    def f32_min_val(self):
        return self.config.f32_min_val

    @property
    def f32_max_val(self):
        return self.config.f32_max_val

    @property
    def i64_min_val(self):
        return self.config.i64_min_val

    @property
    def i64_max_val(self):
        return self.config.i64_max_val

    @property
    def max_dynamic_dim(self):
        return self.config.max_dynamic_dim

    @property
    def ln_f16_max_val(self):
        return self.config.ln_f16_max_val

    @property
    def ln_f32_max_val(self):
        return self.config.ln_f32_max_val

    def compute_safe_average(
        self, constants: list, element_type: Type
    ) -> Optional[float]:
        if len(constants) == 0:
            return None

        sum_value: float = 0.0
        for constant in constants:
            if constant == float("nan"):
                return None
            elif constant == float("+inf"):
                return (
                    self.f16_max_val
                    if isinstance(element_type, ir.F16Type)
                    else self.f32_max_val
                )
            elif constant == float("-inf"):
                return (
                    self.f16_min_val
                    if isinstance(element_type, ir.F16Type)
                    else self.f32_min_val
                )
            else:
                sum_value += float(constant)
        return sum_value / len(constants)

    def get_exp_x(self, x: z3.ArithRef) -> z3.ArithRef:
        """Compute exp(x) using a series expansion."""
        exp_x = 1.0 + (x / 256.0)
        for _ in range(8):
            exp_x *= exp_x
        return exp_x

    def set_range_constraints(
        self,
        value: Optional[z3.ArithRef],
        element_type: Type,
        *,
        min_val: float = None,
        max_val: float = None,
    ):
        if value is None:
            return

        if isinstance(element_type, ir.F16Type):
            max_bound = max_val if max_val is not None else self.f16_max_val
            min_bound = min_val if min_val is not None else self.f16_min_val
        elif isinstance(element_type, ir.F32Type):
            max_bound = max_val if max_val is not None else self.f32_max_val
            min_bound = min_val if min_val is not None else self.f32_min_val
        elif isinstance(element_type, ir.IntegerType) or isinstance(
            element_type, ir.IndexType
        ):
            max_bound = max_val if max_val is not None else self.i64_max_val
            min_bound = min_val if min_val is not None else self.i64_min_val
        else:
            raise ValueError(f"Unsupported element type: {element_type}")
        self.solver.add(value > min_bound, value < max_bound)

    def get_max_ref(self, lhs: z3.ArithRef, rhs: z3.ArithRef) -> z3.ArithRef:
        return z3.If(lhs > rhs, lhs, rhs)

    def get_min_ref(self, lhs: z3.ArithRef, rhs: z3.ArithRef) -> z3.ArithRef:
        return z3.If(lhs < rhs, lhs, rhs)

    def get_max_dim(self, type: ir.RankedTensorType) -> z3.ArithRef:
        """Returns the maximum dimension size as a Z3 integer value.

        If the tensor shape is static, returns the concrete maximum dimension size.
        If the shape is dynamic, returns the maximum between the largest dimension
        and the preset maximum dynamic dimension size (self.max_dynamic_dim).
        """
        max_component = max(type.shape)
        if type.has_static_shape:
            return z3.IntVal(max_component)
        return z3.IntVal(max(max_component, self.max_dynamic_dim))

    @singledispatchmethod
    def process_op(self, op):
        return Status.SUCCESS

    @process_op.register(stablehlo.AddOp)
    def _(self, op: stablehlo.AddOp):
        result = self.ref_dict[op.lhs] + self.ref_dict[op.rhs]
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.SubtractOp)
    def _(self, op: stablehlo.SubtractOp):
        result = self.ref_dict[op.lhs] - self.ref_dict[op.rhs]
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.MulOp)
    def _(self, op: stablehlo.MulOp):
        result = self.ref_dict[op.lhs] * self.ref_dict[op.rhs]
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.DivOp)
    def _(self, op: stablehlo.DivOp):
        rhs = self.ref_dict[op.rhs]
        self.solver.add(rhs != 0)
        result = self.ref_dict[op.lhs] / rhs
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.MaxOp)
    def _(self, op: stablehlo.MaxOp):
        result = self.get_max_ref(self.ref_dict[op.lhs], self.ref_dict[op.rhs])
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.MinOp)
    def _(self, op: stablehlo.MinOp):
        result = self.get_min_ref(self.ref_dict[op.lhs], self.ref_dict[op.rhs])
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.ConstantOp)
    def _(self, op: stablehlo.ConstantOp):
        cst = op.value
        assert isinstance(cst, ir.DenseElementsAttr)
        constants = None
        if cst.is_splat:
            constants = [cst.get_splat_value().value]
        else:
            constants = list(cst)

        val = self.compute_safe_average(constants, cst.type.element_type)
        if val is None:
            return Status.FAILURE
        self.ref_dict[op.output] = z3.RealVal(val)
        return Status.SUCCESS

    @process_op.register(stablehlo.DotOp)
    def _(self, op: stablehlo.DotOp):
        lhs_type = op.lhs.type
        assert isinstance(lhs_type, ir.RankedTensorType)
        if lhs_type.is_dynamic_dim(1):
            return Status.FAILURE  # Cannot process dynamic dimensions
        result = (
            self.ref_dict[op.lhs] * self.ref_dict[op.rhs] * z3.IntVal(lhs_type.shape[1])
        )
        self.set_range_constraints(result, op.lhs.type.element_type)
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
                result *= z3.IntVal(self.max_dynamic_dim)
            else:
                result *= z3.IntVal(lhs_type.shape[dim])
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.RsqrtOp)
    def _(self, op: stablehlo.RsqrtOp):
        operand = self.ref_dict[op.operand]
        element_type = op.operand.type.element_type
        result = 1 / z3.Sqrt(operand)
        self.set_range_constraints(result, element_type, min_val=0.0)
        self.set_range_constraints(operand, element_type, min_val=0.0)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.NegOp)
    def _(self, op: stablehlo.NegOp):
        result = -self.ref_dict[op.operand]
        # TODO: Should we add a range constraint here?
        self.set_range_constraints(result, op.operand.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.ExpOp)
    def _(self, op: stablehlo.ExpOp):
        #! We assume the input is <= 0.0 for simplicity.
        operand = self.ref_dict[op.operand]
        result = z3.Real(op.result.get_name())
        self.ref_dict[op.result] = result
        element_type = op.operand.type.element_type

        self.solver.add(operand <= 0.0)  # Ensure the operand is non-positive
        self.set_range_constraints(result, element_type, min_val=0.0, max_val=1.0)

        return Status.SUCCESS

    @process_op.register(stablehlo.CompareOp)
    def _(self, op: stablehlo.CompareOp):
        lhs = self.ref_dict[op.lhs]
        rhs = self.ref_dict[op.rhs]
        # ? Should we just return a boolean for simplicity?
        compare = stablehlo.ComparisonDirectionAttr(op.comparison_direction).value
        if compare == "EQ":
            self.ref_dict[op.result] = lhs == rhs
        elif compare == "NE":
            self.ref_dict[op.result] = lhs != rhs
        elif compare == "LT":
            self.ref_dict[op.result] = lhs < rhs
        elif compare == "LE":
            self.ref_dict[op.result] = lhs <= rhs
        elif compare == "GT":
            self.ref_dict[op.result] = lhs > rhs
        elif compare == "GE":
            self.ref_dict[op.result] = lhs >= rhs
        else:
            raise ValueError(f"Unsupported comparison direction: {compare}")
        return Status.SUCCESS

    @process_op.register(stablehlo.ConcatenateOp)
    def _(self, op: stablehlo.ConcatenateOp):
        dimension = op.dimension.value
        operands = [self.ref_dict[operand] for operand in op.inputs]

        sum_value = None
        sum_dim_size = 0
        for operand, input in zip(operands, op.inputs):
            dim_size = input.type.shape[dimension]
            if input.type.is_dynamic_dim(dimension):
                dim_size = self.max_dynamic_dim
            if sum_value is None:
                sum_value = operand * z3.IntVal(dim_size)
            else:
                sum_value += operand * z3.IntVal(dim_size)
            sum_dim_size += dim_size
        average_value = sum_value / z3.IntVal(sum_dim_size)

        self.ref_dict[op.result] = average_value
        self.set_range_constraints(average_value, op.result.type.element_type)
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
                    numel = self.max_dynamic_dim
                else:
                    numel *= src_type.shape[dim]
            result = self.ref_dict[src] * z3.IntVal(numel)
            self.set_range_constraints(result, src_type.element_type)
            self.ref_dict[op.result] = result
        elif isinstance(apply_op, stablehlo.MaxOp):
            self.ref_dict[op.result] = self.ref_dict[src]
        else:
            return Status.FAILURE
        return Status.SUCCESS

    @process_op.register(stablehlo.SignOp)
    def _(self, op: stablehlo.SignOp):
        operand = self.ref_dict[op.operand]
        self.ref_dict[op.result] = z3.simplify(
            z3.If(operand > 0, 1, z3.If(operand < 0, -1, 0))
        )
        return Status.SUCCESS

    @process_op.register(stablehlo.SelectOp)
    def _(self, op: stablehlo.SelectOp):
        condition = self.ref_dict[op.pred]
        true_value = self.ref_dict[op.on_true]
        false_value = self.ref_dict[op.on_false]
        # TODO: Make more precise with ranges.
        result = z3.If(condition, true_value, false_value)
        self.set_range_constraints(result, op.on_true.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.AndOp)
    def _(self, op: stablehlo.AndOp):
        self.ref_dict[op.result] = z3.And(self.ref_dict[op.lhs], self.ref_dict[op.rhs])
        return Status.SUCCESS

    @process_op.register(stablehlo.OrOp)
    def _(self, op: stablehlo.OrOp):
        self.ref_dict[op.result] = z3.Or(self.ref_dict[op.lhs], self.ref_dict[op.rhs])
        return Status.SUCCESS

    @process_op.register(stablehlo.XorOp)
    def _(self, op: stablehlo.XorOp):
        self.ref_dict[op.result] = z3.simplify(
            z3.Xor(self.ref_dict[op.lhs], self.ref_dict[op.rhs])
        )
        return Status.SUCCESS

    @process_op.register(stablehlo.NotOp)
    def _(self, op: stablehlo.NotOp):
        self.ref_dict[op.result] = z3.Not(self.ref_dict[op.operand])
        return Status.SUCCESS

    @process_op.register(stablehlo.LogisticOp)
    def _(self, op: stablehlo.LogisticOp):
        # Logistic function: 1 / (1 + exp(-x))
        # However, for simplicity, we just ensure the result is within a reasonable range.
        result = z3.Real(op.result.get_name())
        self.set_range_constraints(
            result, op.result.type.element_type, min_val=0.0, max_val=1.0
        )
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.IsFiniteOp)
    def _(self, op: stablehlo.IsFiniteOp):
        self.ref_dict[op.result] = z3.Bool(op.result.get_name())
        return Status.SUCCESS

    @process_op.register(stablehlo.TanhOp)
    def _(self, op: stablehlo.TanhOp):
        # Tanh function: (exp(x) - exp(-x)) / (exp(x) + exp(-x))
        # For simplicity, we just ensure the result is within a reasonable range.
        result = z3.Real(op.result.get_name())
        self.set_range_constraints(
            result, op.result.type.element_type, min_val=-1.0, max_val=1.0
        )
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.LogOp)
    def _(self, op: stablehlo.LogOp):
        operand = self.ref_dict[op.operand]
        # Logarithm is only defined for positive values.
        self.solver.add(operand > 0.0)
        result = z3.Real(op.result.get_name())
        element_type = op.operand.type.element_type

        if isinstance(element_type, (ir.F16Type, ir.F32Type)):
            max_ln_val = (
                self.ln_f16_max_val
                if isinstance(element_type, ir.F16Type)
                else self.ln_f32_max_val
            )
            self.set_range_constraints(result, element_type, max_val=max_ln_val)
        else:
            raise ValueError(f"Unsupported element type for LogOp: {element_type}")
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.Log1pOp)
    def _(self, op: stablehlo.Log1pOp):
        operand = self.ref_dict[op.operand]
        # Log1p(x) = log(1 + x)
        # We ensure the operand is greater than -1 to avoid log(0).
        self.solver.add(operand > -1.0)
        result = z3.Real(op.result.get_name())
        element_type = op.operand.type.element_type

        if isinstance(element_type, (ir.F16Type, ir.F32Type)):
            max_ln_val = (
                self.ln_f16_max_val
                if isinstance(element_type, ir.F16Type)
                else self.ln_f32_max_val
            )
            self.set_range_constraints(result, element_type, max_val=max_ln_val)
        else:
            raise ValueError(f"Unsupported element type for LogOp: {element_type}")
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.PowOp)
    def _(self, op: stablehlo.PowOp):
        result = self.ref_dict[op.lhs] ** self.ref_dict[op.rhs]
        self.set_range_constraints(result, op.lhs.type.element_type)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(stablehlo.ConvertOp)
    def _(self, op: stablehlo.ConvertOp):
        src = self.ref_dict[op.operand]
        src_element_type = op.operand.type.element_type
        dst_element_type = op.result.type.element_type
        if dst_element_type.width == 1:
            # Convert to boolean
            result = z3.Bool(op.result.get_name())
            self.ref_dict[op.result] = result
            self.solver.add(result == src)
        else:
            if src_element_type.width > dst_element_type.width:
                # If converting to a larger type, we need to set the range constraints.
                self.set_range_constraints(src, dst_element_type)
            self.ref_dict[op.result] = self.ref_dict[op.operand]
        return Status.SUCCESS

    @process_op.register(stablehlo.BroadcastInDimOp)
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
        index_opview = op.index.owner.opview
        if not isinstance(index_opview, arith.ConstantOp):
            return Status.FAILURE

        dim = int(index_opview.literal_value)
        source_type = op.source.type
        max_dim = self.max_dynamic_dim
        result = z3.IntVal(
            max_dim if source_type.is_dynamic_dim(dim) else source_type.shape[dim]
        )
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
        # Set the result to the maximum dimension size for simplicity.
        self.ref_dict[op.result] = self.get_max_dim(arg_type)
        # Store the association of the shape with the tensor type.
        # This is useful for operations that depend on the shape.
        self.association_type_dict[op.result] = arg_type.shape
        return Status.SUCCESS

    #! Handle shape dialect operations
    @process_op.register(shape.ConstSizeOp)
    def _(self, op: shape.ConstSizeOp):
        size = op.value
        assert isinstance(size, ir.IntegerAttr)
        self.ref_dict[op.result] = z3.IntVal(size.value)
        return Status.SUCCESS

    @process_op.register(shape.NumElementsOp)
    def _(self, op: shape.NumElementsOp):
        operand = op.shape
        dim_sizes = self.association_type_dict.get(operand)
        if dim_sizes is None:
            return Status.FAILURE

        numel = 1
        for dim in dim_sizes:
            numel *= self.max_dynamic_dim if ir.ShapedType.is_dynamic_size(dim) else dim

        self.ref_dict[op.result] = z3.IntVal(numel)
        return Status.SUCCESS

    @process_op.register(shape.IndexToSizeOp)
    def _(self, op: shape.IndexToSizeOp):
        self.ref_dict[op.result] = self.ref_dict[op.arg]
        return Status.SUCCESS

    @process_op.register(shape.DivOp)
    def _(self, op: shape.DivOp):
        lhs = self.ref_dict[op.lhs]
        rhs = self.ref_dict[op.rhs]
        self.solver.add(rhs != 0)  # Ensure no division by zero
        result = z3.simplify(lhs / rhs)
        self.ref_dict[op.result] = result
        return Status.SUCCESS

    @process_op.register(shape.FromExtentsOp)
    def _(self, op: shape.FromExtentsOp):
        dim_sizes = []
        for extent in op.extents:
            dim_size = z3.simplify(self.ref_dict[extent]).as_long()
            if dim_size < 0:
                logger.error(f"Negative dimension size encountered: {dim_size}")
                return Status.FAILURE
            dim_sizes.append(dim_size)

        self.association_type_dict[op.result] = dim_sizes
        return Status.SUCCESS

    @process_op.register(shape.ToExtentTensorOp)
    def _(self, op: shape.ToExtentTensorOp):
        dim_sizes = self.association_type_dict.get(op.input)
        if dim_sizes is None:
            logger.error(f"Dimension sizes not found for input: {op.input}")
            return Status.FAILURE
        max_dim_size = max(dim_sizes)
        self.ref_dict[op.result] = z3.IntVal(max_dim_size)
        return Status.SUCCESS

    # TODO: handle other operations as needed
    @process_op.register(stablehlo.AbsOp)
    @process_op.register(stablehlo.ConvolutionOp)
    @process_op.register(stablehlo.FftOp)
    @process_op.register(stablehlo.FloorOp)
    @process_op.register(stablehlo.GetTupleElementOp)
    @process_op.register(stablehlo.GetDimensionSizeOp)
    @process_op.register(stablehlo.ImagOp)
    @process_op.register(stablehlo.InfeedOp)
    @process_op.register(stablehlo.IotaOp)
    @process_op.register(stablehlo.OutfeedOp)
    @process_op.register(stablehlo.OptimizationBarrierOp)
    @process_op.register(stablehlo.PartitionIdOp)
    @process_op.register(stablehlo.PopulationCountOp)
    @process_op.register(stablehlo.RealOp)
    @process_op.register(stablehlo.ReverseOp)
    @process_op.register(stablehlo.SineOp)
    @process_op.register(stablehlo.TupleOp)
    @process_op.register(stablehlo.WhileOp)
    def _(self, op):
        raise NotImplementedError(
            f"Operation {op.name} is not implemented in OpVisitor."
        )

    def visit_op(self, op: ir.Operation):
        """
        Visit an operation and process it based on its type.
        """
        try:
            return self.process_op(op)
        except Exception as e:
            print(f"Error processing operation {op}: {e}")
            raise e
