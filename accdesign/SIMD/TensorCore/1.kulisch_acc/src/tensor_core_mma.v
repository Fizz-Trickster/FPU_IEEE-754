//
// 4x4 행렬 곱셈-누적(MMA) 모듈
// A, B는 각각 4x4 행렬, C는 그 결과
//
module tensor_core_mma #(
    parameter NUM    = 4,        // Number of elements: 4
    parameter DWIDTH = 16,       // FP16 bit-width: 16-bit
    parameter EWIDTH = 5,        // FP16 exponent bit-width: 5-bit
    parameter MWIDTH = 10,       // FP16 mantissa bit-width: 10-bit
    parameter AWIDTH = 92        // Accumulation bit-width: 92-bit (1(sign) + 11(k) + 32(integer) + 48(fraction))
)(
    input       [NUM-1:0][DWIDTH-1:0] A_in, // row
    input       [NUM-1:0][DWIDTH-1:0] B_in, // column
    input                [AWIDTH-1:0] C_in,  
    output               [AWIDTH-1:0] C_out  
);

  // 행렬 A, B에서 각 원소 추출
  // A_ij: A의 (i,j) 원소, B_ij: B의 (i,j) 원소
  // 4x4 행렬 -> index: A[i][j], i,j = 0..3
  // 예시) A[0][0] = A[(0*4 + 0)*DWIDTH +: DWIDTH]

  wire  signed [NUM-1:0][1*EWIDTH+0:0] mul_exp;

  wire         [NUM-1:0][2*MWIDTH+1:0] mul_sum;
  wire         [NUM-1:0][2*MWIDTH+1:0] mul_carry;

  wire         [NUM-1:0]               Exception;
  wire         [NUM-1:0]               Overflow;
  wire         [NUM-1:0]               Underflow;

  genvar i;
  generate
    for (i = 0; i < NUM; i = i + 1) begin : mul_booth
      // 1. fp16 booth multiplier
      fp16_mul_booth #(
        .DWIDTH       (DWIDTH),
        .EWIDTH       (5),
        .MWIDTH       (10)
      ) u_fp16_mul_booth (
          .a_operand      (A_in       [i]
      ),  .b_operand      (B_in       [i]

      ),  .o_sum          (mul_sum    [i]
      ),  .o_carry        (mul_carry  [i]
      ),  .o_exponent     (mul_exp    [i]

      ),  .Exception      (Exception  [i]
      ),  .Overflow       (Overflow   [i]
      ),  .Underflow      (Underflow  [i]
      ));
    end
  endgenerate

  // 4. kulisch accumulation
  wire  [1:0][DWIDTH-1:0] add_result;
  wire  [1:0]             add_exception;


kulisch_acc_fp16 #(
    .NUM             ( NUM     ),
    .DWIDTH          ( DWIDTH  ),
    .EWIDTH          ( EWIDTH  ),
    .MWIDTH          ( MWIDTH  ),
    .AWIDTH          ( AWIDTH  )
) u_kulisch_acc_fp16 (
    .clk,            ( clk      // i                       
),  .rst_n,          ( rst_n    // i                       
                  
),  .i_sum_mul,      ( mul_sum       // i [NUM-1:0][DWIDTH-1:0]  
),  .i_carry_mul,    ( mul_carry     // i [NUM-1:0][DWIDTH-1:0]  
),  .i_exp_mul,      ( mul_exp     // i [NUM-1:0][EWIDTH+1:0]  
                  
),  .i_sum_acc,      (     // i          [AWIDTH-1:0]  
),  .i_carry_acc,    (     // i          [AWIDTH-1:0]  
                  
),  .o_sum_acc,      (     // o          [AWIDTH-1:0]  
),  .o_carry_acc     (     // o          [AWIDTH-1:0]  
));

endmodule
