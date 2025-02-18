`timescale 1ns / 1ps

// Reference:
// https://numeral-systems.com/ieee-754-multiply/

module fp16_mul_booth #(
  parameter DWIDTH = 16,
  parameter EWIDTH = 5,
  parameter MWIDTH = 10,
  parameter BIAS   = (1 << (EWIDTH-1)) - 1		// 15 = 2^(5-1)-1
  )(
    input   [1*DWIDTH-1:0]  a_operand,
    input   [1*DWIDTH-1:0]  b_operand,

    output                         o_sign,
    output         [2*MWIDTH+1:0]  o_sum,
    output         [2*MWIDTH+1:0]  o_carry,
    output  signed [  EWIDTH+0:0]  o_exponent
  );

wire                sign;

wire [1*MWIDTH+0:0] operand_a;
wire [1*MWIDTH+0:0] operand_b;

wire [2*MWIDTH+1:0] product_sum; 
wire [2*MWIDTH+1:0] product_carry; 
wire [1*EWIDTH+0:0] product_exponent;

// sign operation
assign sign = a_operand[DWIDTH-1] ^ b_operand[DWIDTH-1];

// Assigining significand values according to Hidden Bit.
// If exponent is equal to zero then hidden bit will be 0 for that respective significand else it will be 1

// Mantissa operation
assign operand_a = (|a_operand[MWIDTH+:EWIDTH]) ? {1'b1, a_operand[0+:MWIDTH]} : {1'b0, a_operand[0+:MWIDTH]};
assign operand_b = (|b_operand[MWIDTH+:EWIDTH]) ? {1'b1, b_operand[0+:MWIDTH]} : {1'b0, b_operand[0+:MWIDTH]};

// Multiply Mantissa by Radix-4 Booth Multiplier
r4_mb11 #(
 .WIDTH (MWIDTH+1)
  ) u_r4_mb11 (
      .CLK        (1'b0
  ),  .RST        (1'b0
  ),  .mx         (operand_a     
  ),  .my         (operand_b     
  ),  .sum        (product_sum     
  ),  .carry      (product_carry    
	));

// Exponent operation
wire [EWIDTH-1:0] exponent_a;
wire [EWIDTH-1:0] exponent_b;

assign exponent_a = (|a_operand[MWIDTH+:EWIDTH]) ? a_operand[MWIDTH+:EWIDTH]-BIAS : -(BIAS-1);
assign exponent_b = (|b_operand[MWIDTH+:EWIDTH]) ? b_operand[MWIDTH+:EWIDTH]-BIAS : -(BIAS-1);

assign product_exponent = exponent_a + exponent_b;

assign o_sum      = product_sum;
assign o_carry    = product_carry;
assign o_exponent = product_exponent;

endmodule