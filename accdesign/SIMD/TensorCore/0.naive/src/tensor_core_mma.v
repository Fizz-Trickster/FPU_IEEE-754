//
// 4x4 행렬 곱셈-누적(MMA) 모듈
// A, B는 각각 4x4 행렬, C는 그 결과
//
module tensor_core_mma #(
    parameter DWIDTH = 16
)(
    input       [0:3][DWIDTH-1:0] A_in, // row
    input       [0:3][DWIDTH-1:0] B_in, // column
    input            [DWIDTH-1:0] C_in,  
    output           [DWIDTH-1:0] C_out  
);

    wire  [0:3][DWIDTH-1:0] mul_result;
    wire  [0:3]             Exception;
    wire  [0:3]             Overflow;
    wire  [0:3]             Underflow;

    // fp16 multiplier
    fp16_mul #(
      .DWIDTH       (DWIDTH),
      .EWIDTH       (5),
      .MWIDTH       (10),
      .BIAS         (15)
    ) u_fp16_mul [0:3] (
        .a_operand      ({A_in       [3], A_in       [2], A_in       [1], A_in       [0]}
    ),  .b_operand      ({B_in       [3], B_in       [2], B_in       [1], B_in       [0]}
    ),  .result         ({mul_result [3], mul_result [2], mul_result [1], mul_result [0]}
    ),  .Exception      ({Exception  [3], Exception  [2], Exception  [1], Exception  [0]}
    ),  .Overflow       ({Overflow   [3], Overflow   [2], Overflow   [1], Overflow   [0]}
    ),  .Underflow      ({Underflow  [3], Underflow  [2], Underflow  [1], Underflow  [0]}
    ));

    wire  [0:1][DWIDTH-1:0] add_result;
    wire  [0:1]             add_exception;

    // adder tree stage 0
    fp16_add #(
      .DWIDTH         (DWIDTH),
      .EWIDTH         (5),
      .MWIDTH         (10),
      .RWIDTH         (3)      // Round Bit-width
    ) u_fp16_add_s0 [0:1] (
        .a_operand      ({mul_result    [2], mul_result    [0]}
    ),  .b_operand      ({mul_result    [3], mul_result    [1]}
    ),  .result         ({add_result    [1], add_result    [0]}
    ),  .Exception      ({add_exception [1], add_exception [0]}
    ));

    wire  [DWIDTH-1:0] final_add_result;
    wire               final_add_exception;

    // adder tree stage 1
    fp16_add #(
      .DWIDTH         (DWIDTH),
      .EWIDTH         (5),
      .MWIDTH         (10),
      .RWIDTH         (3)      // Round Bit-width
    ) u_fp16_add_s1 (
        .a_operand      (add_result    [0]
    ),  .b_operand      (add_result    [1]
    ),  .result         (final_add_result
    ),  .Exception      (final_add_exception
    ));

    // adder tree stage 2
    fp16_add #(
      .DWIDTH         (DWIDTH),
      .EWIDTH         (5),
      .MWIDTH         (10),
      .RWIDTH         (3)      // Round Bit-width
    ) u_fp16_add_s1 (
        .a_operand      (final_add_result
    ),  .b_operand      (C_in
    ),  .result         (C_out
    ),  .Exception      (
    ));

endmodule
