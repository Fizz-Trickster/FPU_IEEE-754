`timescale 1ns / 1ps
// 4x4 행렬 곱셈-누적(MMA) 모듈
// A, B는 각각 4x4 행렬, C는 그 결과
//
module tensor_core_gemm #(
    parameter NUM    = 4,        // Number of elements: 4
    parameter DWIDTH = 16,       // FP16 bit-width : 16-bit
    parameter EWIDTH = 5,        // FP16 bit-width exponent: 5-bit
    parameter MWIDTH = 10,       // FP16 bit-width mantissa: 10-bit
    parameter AWIDTH = 92        // Accumulation bit-width: 92-bit (1(sign) + 11(k) + 32(integer) + 48(fraction))
)(
    input       [NUM-1:0][NUM-1:0][DWIDTH-1:0] A_in,            // 4x4 matrix
    input       [NUM-1:0][NUM-1:0][DWIDTH-1:0] B_in,            // 4x4 matrix

    input       [NUM-1:0][NUM-1:0][AWIDTH-1:0] C_sum_in,        // 4x4 matrix
    input       [NUM-1:0][NUM-1:0][AWIDTH-1:0] C_carry_in,      // 4x4 matrix
    input                                      C_valid_in,

    output      [NUM-1:0][NUM-1:0][AWIDTH-1:0] C_sum_out,       // 4x4 matrix
    output      [NUM-1:0][NUM-1:0][AWIDTH-1:0] C_carry_out      // 4x4 matrix
);

    wire [NUM-1:0][NUM-1:0][DWIDTH-1:0] B_trans = transpose(B_in);

    genvar r, c;
    generate
        for(r = 0; r < NUM; r = r + 1) begin : rowC
            for(c = 0; c < NUM; c = c + 1) begin : colC
                tensor_core_mma #(
                    .NUM            ( NUM              ),
                    .DWIDTH         ( DWIDTH           ),
                    .EWIDTH         ( EWIDTH           ),
                    .MWIDTH         ( MWIDTH           ),
                    .AWIDTH         ( AWIDTH           )
                ) u_tensor_core_mma (
                    .A_in           ( A_in       [r]   ),
                    .B_in           ( B_trans    [c]   ),

                    .C_sum_in       ( C_sum_in   [r][c]),
                    .C_carry_in     ( C_carry_in [r][c]),
                    .C_valid_in     ( C_valid_in       ),

                    .C_sum_out      ( C_sum_out  [r][c]),
                    .C_carry_out    ( C_carry_out[r][c])
                );
            end
        end
    endgenerate

  function [NUM-1:0][NUM-1:0][DWIDTH-1:0] transpose;
    input [NUM-1:0][NUM-1:0][DWIDTH-1:0] matrix;

    begin
      for(int r = 0; r < NUM; r = r + 1) begin : rowC
        for(int c = 0; c < NUM; c = c + 1) begin : colC
            transpose[r][c] = matrix[c][r];
        end
      end
    end
  endfunction
endmodule
