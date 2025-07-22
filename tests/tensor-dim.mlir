module {
  func.func @tensor_dim(%arg0: tensor<16x16x16xf32>)  {
    %c0 = arith.constant 0 : index
    %dim = tensor.dim %arg0, %c0 : tensor<16x16x16xf32>
    return
  }
}