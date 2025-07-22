import mlir.dialects.stablehlo as stablehlo
import mlir.ir as ir

if __name__ == "__main__":
    import sys
    from stablehlo_solver.solver import MLIRSolver

    if len(sys.argv) != 2:
        print("Usage: python stable_stat.py <mlir_model_file>")
        sys.exit(1)

    model_file = sys.argv[1]
    with open(model_file, "r") as f:
        model_str = f.read()

    with ir.Context() as ctx:
      stablehlo.register_dialect(ctx)
      stablehlo.register_stablehlo_passes()
      module = ir.Module.parse(model_str)
      func = module.body.operations[0]
      op_dict = {}
    
      for op in func.body.blocks[0].operations:
          op_dict[op.name] = op_dict.get(op.name, 0) + 1
          
      print("Operation counts (sorted):")
      # 对字典的键进行排序，按字母顺序输出
      for op_name in sorted(op_dict.keys()):
          print(f"{op_name}: {op_dict[op_name]}")
