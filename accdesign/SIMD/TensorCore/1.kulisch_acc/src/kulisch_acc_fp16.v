module kulisch_acc_fp16 #(
  parameter NUM    = 4,
  parameter DWIDTH = 16,
  parameter EWIDTH = 5,
  parameter MWIDTH = 10,
  parameter BIAS   = (1 << (EWIDTH-1)) - 1,   // 15 = 2^(5-1)-1
  parameter AWIDTH = 92                       // Accumulation bit-width: 92-bit (1(sign) + 11(k) + 32(integer) + 48(fraction))
)(
    input                                 clk,
    input                                 rst_n,

    input         [NUM-1:0][2*MWIDTH+1:0] i_sum_mul,    // input fp16 data
    input         [NUM-1:0][2*MWIDTH+1:0] i_carry_mul,  // input fp16 data
    input  signed [NUM-1:0][1*EWIDTH+0:0] i_exp_mul,


    input                  [AWIDTH-1:0] i_sum_acc,    // kulisch accumulator 
    input                  [AWIDTH-1:0] i_carry_acc,  // kulisch accumulator 

    output                 [AWIDTH-1:0] o_sum_acc,    // kulisch accumulator 
    output                 [AWIDTH-1:0] o_carry_acc   // kulisch accumulator  
);

// FP16 Kulisch Accumulation Example
// Maximum positive value : 0 11110 1111111111
// 1.11 1111 1111 * 2^15 = 65504(FFE0h)
// => 16 
// Minimum positive value : 0 00000 0000000001
// 0.00 0000 0001 * 2^(-14)  
// 0000 0000 0000 0000 0000 0000 1 (0000001h)
// => 25

//------------------------------------------------
// 1. Floating Point to Fixed Point
// 2. Fixed Point Accumulation : Kulisch Accumulation
//------------------------------------------------

//------------------------------------------------
// 1. Shift booth multiplier by exponent
// function [AWIDTH-1:0] f2i;
// [47:00] : fraction
// [77:48] : integer
// [78]    :sign
//------------------------------------------------
reg  signed [NUM-1:0][EWIDTH+1:0] shift_exp;

reg         [NUM-1:0][AWIDTH-1:0] fixed_sum;
reg         [NUM-1:0][AWIDTH-1:0] fixed_carry;

integer k;
always @(*) begin
  for (k = 0; k < NUM; k = k + 1) begin
    shift_exp  [k] = i_exp_mul  [k] + 28;
    fixed_sum  [k] = i_sum_mul  [k] << shift_exp[k];
    fixed_carry[k] = i_carry_mul[k] << shift_exp[k];
  end
end

reg [2*AWIDTH-1:0]         accData_combined;
reg [2*(NUM+0)*AWIDTH-1:0] fixedData_combined;
reg [2*(NUM+1)*AWIDTH-1:0] csa_tree_in;

integer i;
always @(*) begin
  for(i=0; i<NUM; i=i+1) begin
    fixedData_combined[i*2*AWIDTH+:2*AWIDTH] = {fixed_sum[i], fixed_carry[i]};
  end
end

always @(*) begin
  accData_combined = {i_sum_acc, i_carry_acc};
end

always @(*) begin
  csa_tree_in = {accData_combined, fixedData_combined};
end

wire [1*AWIDTH-1:0] csa_tree_out0;
wire [1*AWIDTH-1:0] csa_tree_out1;

NV_DW02_tree #(
    .num_inputs  (2*(NUM+1)),
    .input_width (AWIDTH)
) u_NV_DW02_tree (
    .INPUT (csa_tree_in
),  .OUT0  (csa_tree_out0
),  .OUT1  (csa_tree_out1
));


assign o_sum_acc = csa_tree_out0;
assign o_carry_acc = csa_tree_out1;

endmodule
