module tensor_core_mma #(
  parameter NUM    = 4,        // Number of elements: 4
  parameter DWIDTH = 16,       // FP16 bit-width : 16-bit
  parameter EWIDTH = 5,        // FP16 bit-width exponent: 5-bit
  parameter MWIDTH = 10,       // FP16 bit-width mantissa: 10-bit
  parameter AWIDTH = 92        // Accumulation bit-width: 92-bit (1(sign) + 11(k) + 32(integer) + 48(fraction))
)(
  input       [NUM-1:0][DWIDTH-1:0] A_in,         // row
  input       [NUM-1:0][DWIDTH-1:0] B_in,         // column

  input                [AWIDTH-1:0] C_sum_in,  
  input                [AWIDTH-1:0] C_carry_in,  
  input                             C_valid_in,  

  output               [AWIDTH-1:0] C_sum_out,  
  output               [AWIDTH-1:0] C_carry_out  
);

// C_out = A_in * B_in + C_in 

// 행렬 A, B에서 각 원소 추출
// A_ij: A의 (i,j) 원소, B_ij: B의 (i,j) 원소
// 4x4 행렬 -> index: A[i][j], i,j = 0..3
// 예시) A[0][0] = A[(0*4 + 0)*DWIDTH +: DWIDTH]

wire         [NUM-1:0]               mul_sign;   // mantissa 곱셈 결과 sign
wire         [NUM-1:0][2*MWIDTH+1:0] mul_sum;    // mantissa 곱셈 결과 sum
wire         [NUM-1:0][2*MWIDTH+1:0] mul_carry;  // mantissa 곱셈 결과 carry
wire  signed [NUM-1:0][1*EWIDTH+0:0] mul_exp;    // mantissa 곱셈 결과 exponent

// 1. fp16 booth multiplier
genvar i;
generate
  for (i = 0; i < NUM; i = i + 1) begin : mul_booth
    fp16_mul_booth #(
      .DWIDTH          (DWIDTH),
      .EWIDTH          (EWIDTH),
      .MWIDTH          (MWIDTH)
    ) u_fp16_mul_booth (
        .a_operand     (A_in       [i]
    ),  .b_operand     (B_in       [i]

    ),  .o_sum         (mul_sum    [i]
    ),  .o_carry       (mul_carry  [i]
    ),  .o_sign        (mul_sign   [i]
    ),  .o_exponent    (mul_exp    [i]
    ));
  end
endgenerate

// 4. kulisch accumulation
wire  [1*AWIDTH-1:0] kulisch_sum_acc;
wire  [1*AWIDTH-1:0] kulisch_carry_acc;

wire  [1*AWIDTH-1:0] final_sum_acc;
wire  [1*AWIDTH-1:0] final_carry_acc;
reg   [1*AWIDTH-1:0] final_sum_acc_d;
reg   [1*AWIDTH-1:0] final_carry_acc_d;

assign kulisch_sum_acc   = C_valid_in ? C_sum_in : final_sum_acc_d;
assign kulisch_carry_acc = C_valid_in ? C_carry_in : final_carry_acc_d;

kulisch_acc_fp16 #(
    .NUM             ( NUM     ),
    .DWIDTH          ( DWIDTH  ),
    .EWIDTH          ( EWIDTH  ),
    .MWIDTH          ( MWIDTH  ),
    .AWIDTH          ( AWIDTH  )
) u_kulisch_acc_fp16 (
    .clk,            ( clk                  // i                       
),  .rst_n,          ( rst_n                // i                       
                  
),  .i_sign_mul,     ( mul_sign             // i [NUM-1:0]  
),  .i_sum_mul,      ( mul_sum              // i [NUM-1:0][DWIDTH-1:0]  
),  .i_carry_mul,    ( mul_carry            // i [NUM-1:0][DWIDTH-1:0]  
),  .i_exp_mul,      ( mul_exp              // i [NUM-1:0][EWIDTH+1:0]  
                  
),  .i_sum_acc,      ( kulisch_sum_acc      // i          [AWIDTH-1:0]  
),  .i_carry_acc,    ( kulisch_carry_acc    // i          [AWIDTH-1:0]  
                  
),  .o_sum_acc,      ( final_sum_acc        // o          [AWIDTH-1:0]  
),  .o_carry_acc     ( final_carry_acc      // o          [AWIDTH-1:0]  
));

always @(posedge clk, negedge rst_n) begin
  if (!rst_n) begin
    final_sum_acc_d   <= 0;
    final_carry_acc_d <= 0;
  end else begin
    final_sum_acc_d   <= final_sum_acc;
    final_carry_acc_d <= final_carry_acc;
  end
end

assign C_sum_out   = final_sum_acc_d;
assign C_carry_out = final_carry_acc_d;

endmodule
