///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//File Name: Multiplication.v
//Created By: Sheetal Swaroop Burada
//Date: 30-04-2019
//Project Name: Design of 32 Bit Floating Point ALU Based on Standard IEEE-754 in Verilog and its implementation on FPGA.
//University: Dayalbagh Educational Institute
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

module fp8_mul #(
  parameter DWIDTH = 8,
  parameter EWIDTH = 4,
  parameter MWIDTH = 3
  )(
		input   [DWIDTH-1:0]  a_operand,
		input   [DWIDTH-1:0]  b_operand,
		output  [DWIDTH-1:0]  result,
		output                Exception,
		output                Overflow,
		output                Underflow
		);

wire        sign;
wire        product_round;
wire        normalised;
wire        zero;

wire [MWIDTH:0]     operand_a;
wire [MWIDTH:0]     operand_b;

wire [2*MWIDTH+1:0] product; 
wire [2*MWIDTH+1:0] product_normalised; 


wire [8:0] exponent,sum_exponent;
wire [22:0] product_mantissa;


// sign operation
assign sign = a_operand[DWIDTH-1] ^ b_operand[DWIDTH-1];

//Exception flag sets 1 if either one of the exponent is all 1's.
assign Exception = (&a_operand[MWIDTH+:EWIDTH]) | (&b_operand[MWIDTH+:EWIDTH]);

//Assigining significand values according to Hidden Bit.
//If exponent is equal to zero then hidden bit will be 0 for that respective significand else it will be 1

assign operand_a = (|a_operand[MWIDTH+:EWIDTH]) ? {1'b1,a_operand[0+:MWIDTH]} : {1'b0,a_operand[0+:MWIDTH]};
assign operand_b = (|b_operand[MWIDTH+:EWIDTH]) ? {1'b1,b_operand[0+:MWIDTH]} : {1'b0,b_operand[0+:MWIDTH]};

assign product = operand_a * operand_b;			//Calculating Product

assign product_round = |product_normalised[22:0];  //Ending 22 bits are OR'ed for rounding operation.

assign normalised = product[47] ? 1'b1 : 1'b0;	

assign product_normalised = normalised ? product : product << 1;	//Assigning Normalised value based on 48th bit

//Final Manitssa.
assign product_mantissa = product_normalised[46:24] + (product_normalised[23] & product_round); 

assign zero = Exception ? 1'b0 : (product_mantissa == 23'd0) ? 1'b1 : 1'b0;

assign sum_exponent = a_operand[30:23] + b_operand[30:23];

assign exponent = sum_exponent - 8'd127 + normalised;

assign Overflow = ((exponent[8] & !exponent[7]) & !zero) ; //If overall exponent is greater than 255 then Overflow condition.
//Exception Case when exponent reaches its maximu value that is 384.

//If sum of both exponents is less than 127 then Underflow condition.
assign Underflow = ((exponent[8] & exponent[7]) & !zero) ? 1'b1 : 1'b0; 

assign result = Exception ? 32'd0 : zero ? {sign,31'd0} : Overflow ? {sign,8'hFF,23'd0} : Underflow ? {sign,31'd0} : {sign,exponent[7:0],product_mantissa};


endmodule