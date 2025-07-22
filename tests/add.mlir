module {
  func.func @main(%arg0: tensor<1xf32>, %arg1: tensor<1xf32>) -> tensor<1xf32> {
    %0 = stablehlo.add %arg0, %arg1 : tensor<1xf32>
    return %0 : tensor<1xf32>
  }
}