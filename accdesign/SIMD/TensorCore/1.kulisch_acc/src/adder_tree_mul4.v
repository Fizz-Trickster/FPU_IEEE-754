
module adder_tree_mul4 #(
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

    input  [0:3][DWIDTH-1:0] i_sum_mul,    // input fp16 data
    input  [0:3][DWIDTH-1:0] i_carry_mul,    // input fp16 data

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

NV_DW02_tree #(
    .num_inputs (8),
    .input_width (DWIDTH)
) u_NV_DW02_tree (
    .INPUT (i_sum_mul),
    .OUT0 (o_sum),
    .OUT1 (o_carry)
);


wire [AWIDTH-1:0] fixed_data = f2i(i_fp_data);


always @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        o_kulisch_acc <= {AWIDTH{1'b0}};
    end else if (i_init) begin
        o_kulisch_acc <= i_init_acc + fixed_data;
    end else begin
        o_kulisch_acc <= o_kulisch_acc + fixed_data;
    end
end


//------------------------------------------------
// 1. Floating Point to Fixed Point
// function [AWIDTH-1:0] f2i;
// [47:00] : fraction
// [77:48] : integer
// [78]    :sign
//------------------------------------------------
function [AWIDTH-1:0] f2i;
    input [DWIDTH-1:0] fp16_in;
    localparam FP16_MIN = 24;
    
    reg               sign;
    reg [EWIDTH-1:0]  exponent;
    reg [MWIDTH-1:0]  fraction;
    reg [MWIDTH+0:0]  mantissa;
    
    reg signed [EWIDTH+0:0] shift;       // min -24, max 15

    reg [AWIDTH-1:0] shifted_mantissa;
    reg [AWIDTH-1:0] fixed_val;  
    
    begin
        sign     = fp16_in[DWIDTH-1];
        exponent = fp16_in[MWIDTH+:EWIDTH];
        fraction = fp16_in[0+:MWIDTH];

        if(exponent == 0) begin
            mantissa = {1'b0, fraction}; 
            shift = (exponent+1) - BIAS;
        end else begin
            mantissa = {1'b1, fraction}; 
            shift = (exponent+0) - BIAS;
        end

        // mantissa(11비트)를 기준으로, E>0이면 왼쪽 shift, E<0이면 오른쪽 shift
        // mantissa는 unsigned. sign은 나중에 적용.
        shifted_mantissa = mantissa << ((2*FP16_MIN)-MWIDTH); 

        if(shift[EWIDTH] == 0) begin // shift : positive
            fixed_val = shifted_mantissa << shift; 
        end else begin               // shift : negative
            fixed_val = shifted_mantissa >> (~shift+1); // shift의 절댓값만큼 >> shift
        end

        if(sign) begin
            f2i = ~fixed_val + 1;   // negative
        end else begin
            f2i = fixed_val;
        end
    end
endfunction


endmodule
