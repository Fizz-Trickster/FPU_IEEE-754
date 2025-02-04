//
// 4x4 행렬 곱셈-누적(MMA) 모듈
// A, B는 각각 4x4 행렬, C는 그 결과
//
module tensor_core_mma #(
    parameter DWIDTH = 16,
    parameter AWIDTH = 91
)(
    input       [0:3][DWIDTH-1:0] A_in, // row
    input       [0:3][DWIDTH-1:0] B_in, // column
    input            [AWIDTH-1:0] C_in,  
    output           [AWIDTH-1:0] C_out  
);

    // 행렬 A, B에서 각 원소 추출
    // A_ij: A의 (i,j) 원소, B_ij: B의 (i,j) 원소
    // 4x4 행렬 -> index: A[i][j], i,j = 0..3
    // 예시) A[0][0] = A[(0*4 + 0)*DWIDTH +: DWIDTH]

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
    //// kulisch accumulation
    //kulisch_acc_fp16 #(
    //  .DWIDTH         (DWIDTH),
    //  .EWIDTH         (5),
    //  .MWIDTH         (10),
    //  .BIAS           (15),
    //  .WWIDTH         (79),
    //  .VWIDTH         (12),
    //  .AWIDTH         (AWIDTH)
    //) u_kulisch_acc_fp16(
    //    .clk           (clk
    //),  .rst_n         (rst_n
    //),  .i_fp_data     (final_add_result    // input fp16 data
    //),  .i_init_acc    (C_in                // initial accumulation value
    //),  .i_init        (1'b0                // initial accumulation
    //),  .o_kulisch_acc (C_out               // accumulated value
    //));




    //genvar i, j;
    //generate
    //    for(i = 0; i < 4; i = i + 1) begin : ROW
    //        for(j = 0; j < 4; j = j + 1) begin : COL
    //            // 각 원소를 A_in, B_in에서 추출
    //            assign A_mat[i][j] = A[((i*4 + j)*DWIDTH) +: DWIDTH];
    //            assign B_mat[i][j] = B[((i*4 + j)*DWIDTH) +: DWIDTH];
    //        end
    //    end
    //endgenerate

    //// C = A x B (4x4 행렬 곱셈)
    //// C[i][j] = Σ_k (A[i][k] * B[k][j]),  k = 0..3
    //// 여기서는 각 원소를 signed 정수 곱으로 단순 처리

    //genvar r, c, k;
    //generate
    //    for(r = 0; r < 4; r = r + 1) begin : rowC
    //        for(c = 0; c < 4; c = c + 1) begin : colC
    //            // 누산용 임시 레지스터
    //            reg signed [2*DWIDTH-1:0] sum; // 곱셈 결과가 더 클 수 있으므로 2*DWIDTH로 잡음
    //            always @(*) begin
    //                sum = 0;
    //                for(k = 0; k < 4; k = k + 1) begin
    //                    sum = sum + (A_mat[r][k] * B_mat[k][c]);
    //                end
    //            end
    //            // 결과를 DWIDTH 크기로 자른다고 가정 (오버플로우는 단순히 자름)
    //            assign C_mat[r][c] = sum[DWIDTH-1:0];
    //        end
    //    end
    //endgenerate

    //// C_mat -> C (직렬화)
    //generate
    //    for(i = 0; i < 4; i = i + 1) begin : row_serial
    //        for(j = 0; j < 4; j = j + 1) begin : col_serial
    //            assign C[((i*4 + j)*DWIDTH) +: DWIDTH] = C_mat[i][j];
    //        end
    //    end
    //endgenerate

endmodule
