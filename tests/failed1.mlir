module {
  func.func @failed1(%arg0: tensor<?x115x116xf32>, %arg1: tensor<580x58xf32>) -> (tensor<?x58xf32>, tensor<3xi32>) attributes {SimpleFusion, _symbolic_batch_dim = {"operand#0" = [1], "operand#1" = []}} {
    %c13340 = shape.const_size 13340
    %c23 = shape.const_size 23
    %c580 = shape.const_size 580
    %c = stablehlo.constant dense<23> : tensor<1xi32>
    %c_0 = stablehlo.constant dense<58> : tensor<1xi32>
    %0 = shape.shape_of %arg0 : tensor<?x115x116xf32> -> tensor<3xindex>
    %1 = shape.num_elements %0 : tensor<3xindex> -> index
    %2 = shape.index_to_size %1
    %3 = shape.div %2, %c13340 : !shape.size, !shape.size -> !shape.size
    %4 = shape.from_extents %3, %c23, %c580 : !shape.size, !shape.size, !shape.size
    %5 = shape.to_extent_tensor %4 : !shape.shape -> tensor<3xindex>
    %6 = shape.div %2, %c580 : !shape.size, !shape.size -> !shape.size
    %7 = shape.from_extents %6, %c580 : !shape.size, !shape.size
    %8 = shape.to_extent_tensor %7 : !shape.shape -> tensor<2xindex>
    %9 = stablehlo.dynamic_reshape %arg0, %8 : (tensor<?x115x116xf32>, tensor<2xindex>) -> tensor<?x580xf32>
    %10 = stablehlo.dot %9, %arg1, precision = [DEFAULT, DEFAULT] : (tensor<?x580xf32>, tensor<580x58xf32>) -> tensor<?x58xf32>
    %11 = arith.index_cast %5 : tensor<3xindex> to tensor<3xi32>
    %12 = stablehlo.slice %11 [0:1] : (tensor<3xi32>) -> tensor<1xi32>
    %13 = stablehlo.concatenate %12, %c, %c_0, dim = 0 : (tensor<1xi32>, tensor<1xi32>, tensor<1xi32>) -> tensor<3xi32>
    return %10, %13 : tensor<?x58xf32>, tensor<3xi32>
  }
}

