module {
  func.func @link_dot(%arg0: tensor<64x64xf16>, %arg1: tensor<64x64xf16>) -> (tensor<64x64xf16>) attributes {SimpleFusion} {
    %0 = stablehlo.dot %arg0, %arg1, precision = [DEFAULT, DEFAULT] : (tensor<64x64xf16>, tensor<64x64xf16>) -> tensor<64x64xf16>
    %1 = stablehlo.dot %0, %arg1, precision = [DEFAULT, DEFAULT] : (tensor<64x64xf16>, tensor<64x64xf16>) -> tensor<64x64xf16>
    %2 = stablehlo.dot %1, %arg1, precision = [DEFAULT, DEFAULT] : (tensor<64x64xf16>, tensor<64x64xf16>) -> tensor<64x64xf16>
    %3 = stablehlo.dot %2, %arg1, precision = [DEFAULT, DEFAULT] : (tensor<64x64xf16>, tensor<64x64xf16>) -> tensor<64x64xf16>
    return %3 : tensor<64x64xf16>
  }
}

