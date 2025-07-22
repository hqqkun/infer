module {
  func.func @select(%arg0: tensor<?xi1>, %arg1: tensor<?xf16>, %arg2: tensor<?xf16>, %arg3: tensor<?xi1>, %arg4: tensor<?xf16>, %arg5: tensor<?xi1>, %arg6: tensor<?xf16>, %arg7: tensor<?xi1>) -> tensor<?xf16> attributes {SimpleFusion, _symbolic_batch_dim = {"operand#0" = [1], "operand#1" = [1], "operand#2" = [1], "operand#3" = [1], "operand#4" = [1], "operand#5" = [1], "operand#6" = [1], "operand#7" = [1]}} {
    %0 = stablehlo.select %arg0, %arg1, %arg2 : tensor<?xi1>, tensor<?xf16>
    %1 = stablehlo.select %arg3, %arg4, %0 : tensor<?xi1>, tensor<?xf16>
    %2 = stablehlo.select %arg5, %arg6, %1 : tensor<?xi1>, tensor<?xf16>
    %3 = stablehlo.select %arg7, %arg6, %2 : tensor<?xi1>, tensor<?xf16>
    return %3 : tensor<?xf16>
  }
}

