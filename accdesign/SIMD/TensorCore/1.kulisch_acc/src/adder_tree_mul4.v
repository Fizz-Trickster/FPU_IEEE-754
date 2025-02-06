
module adder_tree_mul4 #(
  parameter NUM    = 4,
  parameter DWIDTH = 16,
  parameter EWIDTH = 5,
  parameter MWIDTH = 10,
  parameter BIAS   = (1 << (EWIDTH-1)) - 1,   // 15 = 2^(5-1)-1
  parameter WWIDTH = 79,
  parameter VWIDTH = 12,
  parameter AWIDTH = WWIDTH + VWIDTH
)(
    input                    clk,
    input                    rst_n,

    input  [NUM-1:0][DWIDTH-1:0] i_sum_mul,    // input fp16 data
    input  [NUM-1:0][DWIDTH-1:0] i_carry_mul,    // input fp16 data

    output [DWIDTH-1:0]      o_sum,   
    output [DWIDTH-1:0]      o_carry   
);

// Range
// FP08 : 2^(-02-07) ~ 2^(14-07)        : 2^(-09) ~ 2^07
// FP16 : 2^(-09-15) ~ 2^(30-15)        : 2^(-24) ~ 2^15
// FP32 : 2^(-22-127) ~ 2^(254-127)     : 2^(-149) ~ 2^127
// FP64 : 2^(-51-1023) ~ 2^(2046-1023)  : 2^(-1074) ~ 2^1023

// Kulisch Accumulation bit-width (W+V)
// W : bit-width of full range of the product
// V : additional bit-width for overflow 
// FP08 => W: 2*(07+09)+1 = 33
// sign : 1 bit, integer : 14 bit, fraction : 18 bit

// FP16 => W: 2*(15+24)+1 = 79
// sign : 1 bit, integer : 30 bit, fraction : 48 bit

// FP32 => W: 2*(127+149)+1 = 553     V : 86
// sign : 1 bit, integer : 254 bit, fraction : 258 bit

// FP64 => W: 2*(1023+1074)+1 = 4195  V : 92
// sign : 1 bit, integer : 2046 bit, fraction : 2148 bit

// FP16 Kulisch Accumulation Example
// matissa : (10+1) bit * (10+1) bit = 22 bit
// 1(sign) + 11(k) + 32(integer) + 48(fraction) = 92 bit

// Maximum positive value : 0 11110 1111111111
// 1.11 1111 1111 * 2^(15) * 1.11 1111 1111 * 2^(15) 
// FFE0h * FFE0h = FFC0 0400h 
// 11.1111 1111 0000 0000 0001 * 2^(30)
// => 1.1 1111 1111 0000 0000 0001 * 2^(31)

// Minimum positive value : 0 00000 0000000001
// 0.00 0000 0001 * 2^(-14) * 0.00 0000 0001 * 2^(-14)
// 2^(-24) * 2^(-24) = 2^(-48)

//------------------------------------------------
// 1. Floating Point to Fixed Point
// 2. Fixed Point Accumulation : Kulisch Accumulation
//------------------------------------------------

reg [NUM*2*DWIDTH-1:0] csa_tree_in;
integer i;

always @(*) begin
    for(i=0; i<NUM; i=i+1) begin
        csa_tree_in[i*2*DWIDTH+:2*DWIDTH] = {i_sum_mul[i], i_carry_mul[i]};
    end
end

wire [1*DWIDTH-1:0] csa_tree_out0;
wire [1*DWIDTH-1:0] csa_tree_out1;

NV_DW02_tree #(
    .num_inputs  (2*NUM),
    .input_width (DWIDTH)
) u_NV_DW02_tree (
    .INPUT (csa_tree_in
),  .OUT0  (csa_tree_out0
),  .OUT1  (csa_tree_out1
));

endmodule
