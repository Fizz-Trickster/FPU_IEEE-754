///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//File Name: Addition-Subtraction.v
//Created By: Sheetal Swaroop Burada
//Date: 30-04-2019
//Project Name: Design of 32 Bit Floating Point ALU Based on Standard IEEE-754 in Verilog and its implementation on FPGA.
//University: Dayalbagh Educational Institute
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Reference:
// https://numeral-systems.com/ieee-754-add/

module fp32_add #(
  parameter DWIDTH = 32,
  parameter EWIDTH = 8,
  parameter MWIDTH = 23,
	parameter BIAS   = 127,
  parameter RWIDTH = 3      // Round Bit-width
)(
  input   [DWIDTH-1:0]  a_operand, 
  input   [DWIDTH-1:0]  b_operand, 
  output  [DWIDTH-1:0]  result, 
  input                 AddBar_Sub,	//If Add_Sub is low then Addition else Subtraction.
  output                Exception
);

wire operation_sub_addBar;
wire Comp_enable;
wire output_sign;

wire [DWIDTH-1:0] operand_a;
wire [DWIDTH-1:0] operand_b;

wire [MWIDTH+0:0] significand_a;
wire [MWIDTH+0:0] significand_b;

wire [EWIDTH-1:0] exp_a;
wire [EWIDTH-1:0] exp_b;
wire [EWIDTH-1:0] exponent_diff;

wire [MWIDTH+0+RWIDTH:0] significand_a_padded;
wire [MWIDTH+0+RWIDTH:0] significand_b_padded;
wire [MWIDTH+0+RWIDTH:0] significand_b_add_sub;
wire [MWIDTH+1+RWIDTH:0] significand_add;
wire [MWIDTH+1+RWIDTH:0] significand_add_normalized;
wire [EWIDTH+0+MWIDTH-1:0] add_sum;

wire                guard;
wire                round;
wire                sticky;
wire                round_up;


wire [7:0] exponent_b_add_sub;

wire [23:0] significand_sub_complement;
wire [24:0] significand_sub;
wire [30:0] sub_diff;
wire [24:0] subtraction_diff; 
wire [7:0] exponent_sub;

// Floating Point Addition Algorithm
// 1. Convert to exponent to decimal numbers
// 2. Prepend implicit 1 to significand
// 3. Shift binary point to align exponents
// 4. Add significands
// 5. Normalize result
// 6. Round result
// 7. Convert exponent to binary number
// 8. Assemble sign, exponent, and significand

// Prerequisite: Finding the larger operand for operations
// Always, operand_a > operand_b
assign {Comp_enable, operand_a, operand_b} = (a_operand[0+:MWIDTH+EWIDTH] < b_operand[0+:MWIDTH+EWIDTH]) ? 
                                             {1'b1, b_operand, a_operand} : 
                                             {1'b0, a_operand, b_operand} ;

// Extracting exponent from operand
assign exp_a = operand_a[MWIDTH+:EWIDTH];
assign exp_b = operand_b[MWIDTH+:EWIDTH];

//If exponent is equal to zero then hidden bit will be 0 for that respective significand else it will be 1
assign significand_a = (|exp_a) ? {1'b1, operand_a[0+:MWIDTH]} : {1'b0, operand_a[0+:MWIDTH]};
assign significand_b = (|exp_b) ? {1'b1, operand_b[0+:MWIDTH]} : {1'b0, operand_b[0+:MWIDTH]};

//Evaluating Exponent Difference
assign exponent_diff = exp_a - exp_b;

// significand_a,b를 확장하고 하위 비트를 0으로 채움
assign significand_a_padded = {significand_a, {RWIDTH{1'b0}}};
assign significand_b_padded = {significand_b, {RWIDTH{1'b0}}};

// Right shift 수행
assign significand_b_add_sub = significand_b_padded >> exponent_diff;

//Checking exponents are same or not
assign exponent_b_add_sub = operand_b[30:23] + exponent_diff; 
assign perform = (operand_a[30:23] == exponent_b_add_sub);

// Add significands
assign significand_add = (perform & operation_sub_addBar) ? (significand_a_padded + significand_b_add_sub) : 'd0; 

// Normalize result
// If carry generates in sum value then exponent must be added with 1 else feed as it is.
assign add_sum[MWIDTH+:EWIDTH] = significand_add[MWIDTH+1+RWIDTH] ? (1'b1 + exp_a) : exp_a;
assign significand_add_normalized = significand_add[MWIDTH+1+RWIDTH] ? significand_add : significand_add << 1;

// Round result
assign guard  = significand_add_normalized[RWIDTH];        // guard bit는 normalised 결과의 MWIDTH 비트
assign round  = significand_add_normalized[RWIDTH-1];        // round bit는 그 다음 비트
assign sticky = |significand_add_normalized[RWIDTH-2:0];     // sticky bit는 나머지 하위 비트들의 OR

assign round_up = guard & (round | sticky) | (!round & !sticky & significand_add_normalized[RWIDTH]);

assign add_sum[0+:MWIDTH] = significand_add_normalized[RWIDTH+1+:MWIDTH] + round_up;



///////////////////////////////////////////////////////////////////////////////////////////////////////
//Exception flag sets 1 if either one of the exponent is 255.
assign Exception = (&exp_a) | (&exp_b);

assign output_sign = AddBar_Sub ? Comp_enable ? !operand_a[31] : operand_a[31] : operand_a[31] ;

assign operation_sub_addBar = AddBar_Sub ? operand_a[31] ^ operand_b[31] : ~(operand_a[31] ^ operand_b[31]);

//Assigining significand values according to Hidden Bit.

///////////////////////////////////////////////////////////////////////////////////////////////////////
//------------------------------------------------SUB BLOCK------------------------------------------//

assign significand_sub_complement = (perform & !operation_sub_addBar) ? ~(significand_b_add_sub) + 24'd1 : 24'd0 ; 

assign significand_sub = perform ? (significand_a + significand_sub_complement) : 25'd0;

priority_encoder pe(significand_sub,operand_a[30:23],subtraction_diff,exponent_sub);

assign sub_diff[30:23] = exponent_sub;

assign sub_diff[22:0] = subtraction_diff[22:0];

///////////////////////////////////////////////////////////////////////////////////////////////////////
//-------------------------------------------------OUTPUT--------------------------------------------//

//If there is no exception and operation will evaluate


assign result = Exception ? 32'b0 : ((!operation_sub_addBar) ? {output_sign,sub_diff} : {output_sign,add_sum});

endmodule
