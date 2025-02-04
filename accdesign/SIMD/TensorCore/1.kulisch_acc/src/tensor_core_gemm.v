`timescale 1ns / 1ps
// 4x4 행렬 곱셈-누적(MMA) 모듈
// A, B는 각각 4x4 행렬, C는 그 결과
//
module tensor_core_gemm #(
    parameter DWIDTH = 16,
    parameter AWIDTH = 91
)(
    input       [0:3][0:3][DWIDTH-1:0] A_in,     // 4x4 matrix
    input       [0:3][0:3][DWIDTH-1:0] B_in,     // 4x4 matrix
    input       [0:3][0:3][AWIDTH-1:0] C_in,     // 4x4 matrix
    input                              in_valid,

    output      [0:3][0:3][AWIDTH-1:0] C_out,    // 4x4 matrix
    output                             out_valid
);

    // 행렬 A, B에서 각 원소 추출
    // A_ij: A의 (i,j) 원소, B_ij: B의 (i,j) 원소
    // 4x4 행렬 -> index: A[i][j], i,j = 0..3
    // 예시) C[0][0] = A[0] * B[0]

    wire [0:3][0:3][DWIDTH-1:0] B_trans = transpose(B_in);

    genvar r, c;
    generate
        for(r = 0; r < 4; r = r + 1) begin : rowC
            for(c = 0; c < 4; c = c + 1) begin : colC
                tensor_core_mma #(
                    .DWIDTH (DWIDTH),
                    .AWIDTH (AWIDTH)
                ) u_tensor_core_mma (
                    .A_in   (A_in   [r]),
                    .B_in   (B_trans[c]),
                    .C_in   (C_in   [r][c]),
                    .C_out  (C_out  [r][c])
                );
            end
        end
    endgenerate

  function [0:3][0:3][DWIDTH-1:0] transpose;
    input [0:3][0:3][DWIDTH-1:0] matrix;

    begin
      for(int r = 0; r < 4; r = r + 1) begin : rowC
        for(int c = 0; c < 4; c = c + 1) begin : colC
            transpose[r][c] = matrix[c][r];
        end
      end
    end
  endfunction
endmodule
