///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//File Name: Multiplication.v
//Created By: Sheetal Swaroop Burada
//Date: 30-04-2019
//Project Name: Design of 32 Bit Floating Point ALU Based on Standard IEEE-754 in Verilog and its implementation on FPGA.
//University: Dayalbagh Educational Institute
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

module fp32_mul #(
  parameter DWIDTH = 32,
  parameter EWIDTH = 8,
  parameter MWIDTH = 23,
	parameter BIAS   = 127
)(
		input   [DWIDTH-1:0]  a_operand,
		input   [DWIDTH-1:0]  b_operand,
		output  [DWIDTH-1:0]  result,
		output                Exception,
		output                Overflow,
		output                Underflow
);

wire        				sign;
wire        				product_round;
wire        				normalized;
wire        				zero;

wire [MWIDTH:0]     operand_a;
wire [MWIDTH:0]     operand_b;

wire [2*MWIDTH+1:0] product; 
wire [2*MWIDTH+1:0] product_normalized; 

wire                guard;
wire                round;
wire                sticky;
wire                round_up;

wire [EWIDTH:0] exponent;
wire [EWIDTH:0] sum_exponent;

wire [MWIDTH-1:0] product_mantissa;


// sign operation
assign sign = a_operand[DWIDTH-1] ^ b_operand[DWIDTH-1];

// Assigining significand values according to Hidden Bit.
// If exponent is equal to zero then hidden bit will be 0 for that respective significand else it will be 1


// Mantissa operation
assign operand_a = (|a_operand[MWIDTH+:EWIDTH]) ? {1'b1, a_operand[0+:MWIDTH]} : {1'b0,a_operand[0+:MWIDTH]};
assign operand_b = (|b_operand[MWIDTH+:EWIDTH]) ? {1'b1, b_operand[0+:MWIDTH]} : {1'b0,b_operand[0+:MWIDTH]};

assign product   = operand_a * operand_b;               // Calculating Product

assign normalized = product[2*MWIDTH+1];
assign product_normalized = normalised ? product : product << 1;	//Assigning Normalised value based on 48th bit

// Mantissa Round 
// Round to nearest even 규칙 구현:
// 1. G = 0 인 경우: round down
// 2. G = 1 인 경우:
//    - R = 1 || S = 1: round up
//    - R = 0 && S = 0: 중간값, LSB가 0이 되도록 round  ex) 11.5 -> 12.0, 12.5 -> 12.0
assign guard  = product_normalized[MWIDTH];          // guard bit는 normalised 결과의 MWIDTH 비트
assign round  = product_normalized[MWIDTH-1];        // round bit는 그 다음 비트
assign sticky = |product_normalized[MWIDTH-2:0];     // sticky bit는 나머지 하위 비트들의 OR

assign round_up = guard & (round | sticky) | (!round & !sticky & product_normalized[MWIDTH+1]);

assign product_mantissa = product_normalized[MWIDTH+1+:MWIDTH] + round_up; 	// Rounding operation

assign zero = Exception ? 1'b0 : (product_mantissa == 'd0) ? 1'b1 : 1'b0;

// Exponent operation
assign sum_exponent = a_operand[MWIDTH+:EWIDTH] + b_operand[MWIDTH+:EWIDTH];
assign exponent = sum_exponent - BIAS + normalized;

// Overflow and Underflow operation
assign Overflow 	= ((exponent[EWIDTH] & !exponent[EWIDTH-1]) & !zero) ; //If overall exponent is greater than 255 then Overflow condition.
assign Underflow  = ((exponent[EWIDTH] &  exponent[EWIDTH-1]) & !zero) ? 1'b1 : 1'b0; 

//Exception flag sets 1 if either one of the exponent is all 1's.
assign Exception = (&a_operand[MWIDTH+:EWIDTH]) | (&b_operand[MWIDTH+:EWIDTH]);

// Result operation
assign result = Exception ? 32'd0 																			: 
								zero      ? {sign, 31'd0} 															: 
								Overflow  ? {sign, 8'hFF,23'd0} 												: 
								Underflow ? {sign, 31'd0} 															: 
								            {sign, exponent[0+:EWIDTH], product_mantissa};


endmodule
