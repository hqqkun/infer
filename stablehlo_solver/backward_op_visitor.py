import mlir.ir as ir
import mlir.dialects.stablehlo as stablehlo
import mlir.dialects.tensor as tensor
import mlir.dialects.arith as arith
import mlir.dialects.shape as shape
import mlir.dialects.func as func
from functools import singledispatchmethod
from queue import Queue


class BackwardOpVisitor:
    """Visitor for backward operations in MLIR using static methods."""

    @staticmethod
    def collect_interested_ops(returnOp) -> set:
        if not isinstance(returnOp, func.ReturnOp):
            return set()

        visited = set()
        work_list = Queue()
        interested_ops = set()

        for arg in returnOp.operands_:
            if arg not in visited:
                visited.add(arg)
                work_list.put(arg)

        while not work_list.empty():
            val = work_list.get()
            if isinstance(val, ir.BlockArgument):
                continue

            val_lst = list(val) if isinstance(val, ir.OpOperandList) else [val]
            for v in val_lst:
                define_op = v.owner
                if define_op is None:
                    continue
                if isinstance(define_op, ir.Operation):
                    interested_ops.add(define_op)
                    BackwardOpVisitor.process_op(define_op.opview, work_list, visited)

        return interested_ops

    @singledispatchmethod
    @staticmethod
    def visit(op):
        raise NotImplementedError(f"Unsupported operation: {op}")

    @visit.register(shape.DivOp)
    @visit.register(stablehlo.AddOp)
    @visit.register(stablehlo.AndOp)
    @visit.register(stablehlo.CompareOp)
    @visit.register(stablehlo.DivOp)
    @visit.register(stablehlo.DotGeneralOp)
    @visit.register(stablehlo.DotOp)
    @visit.register(stablehlo.MaxOp)
    @visit.register(stablehlo.MinOp)
    @visit.register(stablehlo.MulOp)
    @visit.register(stablehlo.OrOp)
    @visit.register(stablehlo.PowOp)
    @visit.register(stablehlo.SubtractOp)
    @visit.register(stablehlo.XorOp)
    @staticmethod
    def _(op):
        return [op.lhs, op.rhs]

    @visit.register(stablehlo.BroadcastInDimOp)
    @visit.register(stablehlo.DynamicBroadcastInDimOp)
    @visit.register(stablehlo.DynamicPadOp)
    @visit.register(stablehlo.DynamicReshapeOp)
    @visit.register(stablehlo.DynamicSliceOp)
    @visit.register(stablehlo.GatherOp)
    @visit.register(stablehlo.PadOp)
    @visit.register(stablehlo.RealDynamicSliceOp)
    @visit.register(stablehlo.ReshapeOp)
    @visit.register(stablehlo.SliceOp)
    @visit.register(stablehlo.TorchIndexSelectOp)
    @visit.register(stablehlo.TransposeOp)
    @staticmethod
    def _(op):
        return [op.operand]

    @visit.register(stablehlo.ConcatenateOp)
    @visit.register(stablehlo.ReduceOp)
    @staticmethod
    def _(op):
        return op.inputs

    @visit.register(stablehlo.SelectOp)
    @staticmethod
    def _(op):
        return [op.pred, op.on_true, op.on_false]

    @visit.register(stablehlo.ConstantOp)
    @visit.register(shape.ConstSizeOp)
    @visit.register(arith.ConstantOp)
    @staticmethod
    def _(op):
        return []

    @visit.register(stablehlo.ConvertOp)
    @visit.register(stablehlo.RsqrtOp)
    @visit.register(stablehlo.NegOp)
    @visit.register(stablehlo.ExpOp)
    @visit.register(stablehlo.SignOp)
    @visit.register(stablehlo.NotOp)
    @visit.register(stablehlo.LogisticOp)
    @visit.register(stablehlo.TanhOp)
    @visit.register(stablehlo.LogOp)
    @visit.register(stablehlo.Log1pOp)
    @staticmethod
    def _(op):
        return [op.operand]

    @visit.register(stablehlo.IsFiniteOp)
    @staticmethod
    def _(op):
        return [op.x]

    @visit.register(tensor.DimOp)
    @staticmethod
    def _(op):
        return [op.source, op.index]

    @visit.register(tensor.ExpandShapeOp)
    @visit.register(tensor.CollapseShapeOp)
    @staticmethod
    def _(op):
        return [op.src]

    @visit.register(tensor.ExtractSliceOp)
    @staticmethod
    def _(op):
        return [op.source]

    @visit.register(arith.IndexCastOp)
    @staticmethod
    def _(op):
        return [op.in_]

    @visit.register(shape.IndexToSizeOp)
    @visit.register(shape.ShapeOfOp)
    @staticmethod
    def _(op):
        return [op.arg]

    @visit.register(shape.NumElementsOp)
    @staticmethod
    def _(op):
        return [op.shape]

    @visit.register(shape.FromExtentsOp)
    @staticmethod
    def _(op):
        return [op.extents]

    @visit.register(shape.ToExtentTensorOp)
    @staticmethod
    def _(op):
        return [op.input]

    @staticmethod
    def process_op(op, work_list: Queue, visited: set):
        operands = BackwardOpVisitor.visit(op)
        for operand in operands:
            if operand not in visited:
                work_list.put(operand)
                visited.add(operand)
