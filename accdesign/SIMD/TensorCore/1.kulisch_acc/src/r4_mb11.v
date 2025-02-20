`timescale 1ns / 1ps

// Radix-4 Booth Multiplier
module r4_mb11 #(
  parameter WIDTH = 11
  )(
    input                       CLK,
    input                       RST,
    input  signed [1*WIDTH-1:0] mx,
    input  signed [1*WIDTH-1:0] my,
    output signed [2*WIDTH-1:0] sum,
    output signed [2*WIDTH-1:0] carry
  );

// group_cnt = ceil(WIDTH/2)
localparam group_cnt = (WIDTH >> 1) + (WIDTH[0] ? 1 : 0); // // for WIDTH=11, group_cnt = 6

wire [group_cnt-1:0] s, d, n;       // single, double, neg
wire [group_cnt-1:0] nze, pze;      // neg zero, pos zero
wire [group_cnt-1:0] e;             // sign extension


//--------------------------------------------------------
// 1. Booth encoding
//--------------------------------------------------------
  booth_encoder b_e0(.x({mx[ 1], mx[ 0], 1'b0}),  .single(s[0]), .double(d[0]), .neg(n[0]), .pzero(pze[0]), .nzero(nze[0]));
  booth_encoder b_e1(.x({mx[ 3], mx[ 2], mx[1]}), .single(s[1]), .double(d[1]), .neg(n[1]), .pzero(pze[1]), .nzero(nze[1]));
  booth_encoder b_e2(.x({mx[ 5], mx[ 4], mx[3]}), .single(s[2]), .double(d[2]), .neg(n[2]), .pzero(pze[2]), .nzero(nze[2]));
  booth_encoder b_e3(.x({mx[ 7], mx[ 6], mx[5]}), .single(s[3]), .double(d[3]), .neg(n[3]), .pzero(pze[3]), .nzero(nze[3]));
  booth_encoder b_e4(.x({mx[ 9], mx[ 8], mx[7]}), .single(s[4]), .double(d[4]), .neg(n[4]), .pzero(pze[4]), .nzero(nze[4]));
  booth_encoder b_e5(.x({mx[10], mx[10], mx[9]}), .single(s[5]), .double(d[5]), .neg(n[5]), .pzero(pze[5]), .nzero(nze[5]));

//--------------------------------------------------------
// 2. Booth Selector를 통한 Partial Product 생성
//--------------------------------------------------------
wire [WIDTH:0] epp2d[0:group_cnt-1];

genvar j;
generate
  for (j = 0; j < group_cnt; j = j + 1) begin: partial_product_gen 
    booth_selector bs0 (.double(d[j]), .shifted(1'b0),   .single(s[j]), .y(my[ 0]), .neg(n[j]), .p(epp2d[j][ 0]));
    booth_selector bs1 (.double(d[j]), .shifted(my[ 0]), .single(s[j]), .y(my[ 1]), .neg(n[j]), .p(epp2d[j][ 1]));
    booth_selector bs2 (.double(d[j]), .shifted(my[ 1]), .single(s[j]), .y(my[ 2]), .neg(n[j]), .p(epp2d[j][ 2]));
    booth_selector bs3 (.double(d[j]), .shifted(my[ 2]), .single(s[j]), .y(my[ 3]), .neg(n[j]), .p(epp2d[j][ 3]));
    booth_selector bs4 (.double(d[j]), .shifted(my[ 3]), .single(s[j]), .y(my[ 4]), .neg(n[j]), .p(epp2d[j][ 4]));
    booth_selector bs5 (.double(d[j]), .shifted(my[ 4]), .single(s[j]), .y(my[ 5]), .neg(n[j]), .p(epp2d[j][ 5]));
    booth_selector bs6 (.double(d[j]), .shifted(my[ 5]), .single(s[j]), .y(my[ 6]), .neg(n[j]), .p(epp2d[j][ 6]));
    booth_selector bs7 (.double(d[j]), .shifted(my[ 6]), .single(s[j]), .y(my[ 7]), .neg(n[j]), .p(epp2d[j][ 7]));
    booth_selector bs8 (.double(d[j]), .shifted(my[ 7]), .single(s[j]), .y(my[ 8]), .neg(n[j]), .p(epp2d[j][ 8]));
    booth_selector bs9 (.double(d[j]), .shifted(my[ 8]), .single(s[j]), .y(my[ 9]), .neg(n[j]), .p(epp2d[j][ 9]));
    booth_selector bs10(.double(d[j]), .shifted(my[ 9]), .single(s[j]), .y(my[10]), .neg(n[j]), .p(epp2d[j][10]));
    booth_selector bs11(.double(d[j]), .shifted(my[10]), .single(s[j]), .y(my[10]), .neg(n[j]), .p(epp2d[j][11]));
  end
endgenerate

//--------------------------------------------------------
// 3. sign extension bit(e[j]) 생성
//--------------------------------------------------------
assign e[0] = nze[0] ? 1'b0 : (~(my[WIDTH-1] ^ n[0]) | pze[0]);
assign e[1] = nze[1] ? 1'b0 : (~(my[WIDTH-1] ^ n[1]) | pze[1]);
assign e[2] = nze[2] ? 1'b0 : (~(my[WIDTH-1] ^ n[2]) | pze[2]);
assign e[3] = nze[3] ? 1'b0 : (~(my[WIDTH-1] ^ n[3]) | pze[3]);
assign e[4] = nze[4] ? 1'b0 : (~(my[WIDTH-1] ^ n[4]) | pze[4]);
assign e[5] = nze[5] ? 1'b0 : (~(my[WIDTH-1] ^ n[5]) | pze[5]);

//--------------------------------------------------------
// 4. partial product에 sign extension bit 붙이기
//--------------------------------------------------------
wire [WIDTH+1:0] fpp0, fpp1, fpp2, fpp3, fpp4, fpp5;

assign fpp0 = {~e[0], epp2d[0]};
assign fpp1 = { e[1], epp2d[1]};
assign fpp2 = { e[2], epp2d[2]};
assign fpp3 = { e[3], epp2d[3]};
assign fpp4 = { e[4], epp2d[4]};
assign fpp5 = { e[5], epp2d[5]};

//--------------------------------------------------------
// 5. partial product 더하기
//    sum, carry 생성
//--------------------------------------------------------

wire [6*WIDTH-1:0] SUM;
wire [6*WIDTH-1:0] CARRY; 
wire [6*WIDTH-1:0] INT_SUM;
wire [6*WIDTH-1:0] INT_CARRY;


  // -------------------------
  // bit 0
  HALF_ADDER HA0(
    .a(fpp0[0]),
    .b(n[0]),
    .sum(INT_SUM[0]),
    .cout(INT_CARRY[0])
  );
  assign SUM[0]   = INT_SUM[0];
  assign CARRY[0] = INT_CARRY[0];

  // -------------------------
  // bit 1
  assign SUM[1]   = fpp0[1];
  assign CARRY[1] = 1'b0;

  // -------------------------
  // bit 2
  FULL_ADDER FA0(
    .a(fpp0[2]),
    .b(fpp1[0]),
    .cin(n[1]),
    .sum(INT_SUM[2]),
    .cout(INT_CARRY[1])
  );
  assign SUM[2]   = INT_SUM[2];
  assign CARRY[2] = INT_CARRY[1];

  // -------------------------
  // bit 3
  HALF_ADDER HA1(
    .a(fpp0[3]),
    .b(fpp1[1]),
    .sum(INT_SUM[3]),
    .cout(INT_CARRY[2])
  );
  assign SUM[3]   = INT_SUM[3];
  assign CARRY[3] = INT_CARRY[2];

  // -------------------------
  // bit 4
  FULL_ADDER FA1(
    .a(fpp0[4]), .b(fpp1[2]), .cin(fpp2[0]),
    .sum(INT_SUM[4]), .cout(INT_CARRY[4])
  );
  HALF_ADDER HA2(
    .a(INT_SUM[4]), .b(n[2]),
    .sum(INT_SUM[5]), .cout(INT_CARRY[3])
  );
  assign SUM[4]   = INT_SUM[5];
  assign CARRY[4] = INT_CARRY[3];

  // -------------------------
  // bit 5
  FULL_ADDER FA2(
    .a(fpp0[5]), .b(fpp1[3]), .cin(fpp2[1]),
    .sum(INT_SUM[6]), .cout(INT_CARRY[6])
  );
  HALF_ADDER HA3(
    .a(INT_SUM[6]), .b(INT_CARRY[4]),
    .sum(INT_SUM[7]), .cout(INT_CARRY[5])
  );
  assign SUM[5]   = INT_SUM[7];
  assign CARRY[5] = INT_CARRY[5];

  // -------------------------
  // bit 6
  FULL_ADDER FA3(
    .a(fpp0[6]), .b(fpp1[4]), .cin(fpp2[2]),
    .sum(INT_SUM[8]), .cout(INT_CARRY[9])
  );
  HALF_ADDER HA4(
    .a(fpp3[0]), .b(n[3]),
    .sum(INT_SUM[9]), .cout(INT_CARRY[8])
  );
  FULL_ADDER FA4(
    .a(INT_SUM[8]), .b(INT_SUM[9]), .cin(INT_CARRY[6]),
    .sum(INT_SUM[10]), .cout(INT_CARRY[7])
  );
  assign SUM[6]   = INT_SUM[10];
  assign CARRY[6] = INT_CARRY[7];

  // -------------------------
  // bit 7
  FULL_ADDER FA5(
    .a(fpp0[7]), .b(fpp1[5]), .cin(fpp2[3]),
    .sum(INT_SUM[11]), .cout(INT_CARRY[12])
  );
  HALF_ADDER HA5(
    .a(fpp3[1]), .b(INT_CARRY[8]),
    .sum(INT_SUM[12]), .cout(INT_CARRY[11])
  );
  FULL_ADDER FA6(
    .a(INT_SUM[11]), .b(INT_SUM[12]), .cin(INT_CARRY[9]),
    .sum(INT_SUM[13]), .cout(INT_CARRY[10])
  );
  assign SUM[7]   = INT_SUM[13];
  assign CARRY[7] = INT_CARRY[10];

  // -------------------------
  // bit 8
  FULL_ADDER FA7(
    .a(fpp0[8]), .b(fpp1[6]), .cin(fpp2[4]),
    .sum(INT_SUM[14]), .cout(INT_CARRY[15])
  );
  FULL_ADDER FA8(
    .a(fpp3[2]), .b(fpp4[0]), .cin(INT_CARRY[11]),
    .sum(INT_SUM[15]), .cout(INT_CARRY[14])
  );
  FULL_ADDER FA9(
    .a(INT_SUM[14]), .b(INT_SUM[15]), .cin(INT_CARRY[12]),
    .sum(INT_SUM[16]), .cout(INT_CARRY[13])
  );
  assign SUM[8]   = INT_SUM[16];
  assign CARRY[8] = INT_CARRY[13];

  // -------------------------
  // bit 9
  FULL_ADDER FA10(
    .a(fpp0[9]), .b(fpp1[7]), .cin(fpp2[5]),
    .sum(INT_SUM[17]), .cout(INT_CARRY[18])
  );
  FULL_ADDER FA11(
    .a(fpp3[3]), .b(fpp4[1]), .cin(INT_CARRY[14]),
    .sum(INT_SUM[18]), .cout(INT_CARRY[17])
  );
  FULL_ADDER FA12(
    .a(INT_SUM[17]), .b(INT_SUM[18]), .cin(INT_CARRY[15]),
    .sum(INT_SUM[19]), .cout(INT_CARRY[16])
  );
  assign SUM[9]   = INT_SUM[19];
  assign CARRY[9] = INT_CARRY[16];

  // -------------------------
  // bit 10
  FULL_ADDER FA13(
    .a(fpp0[10]), .b(fpp1[8]), .cin(fpp2[6]),
    .sum(INT_SUM[20]), .cout(INT_CARRY[21])
  );
  FULL_ADDER FA14(
    .a(fpp3[4]), .b(fpp4[2]), .cin(INT_CARRY[17]),
    .sum(INT_SUM[21]), .cout(INT_CARRY[20])
  );
  FULL_ADDER FA15(
    .a(INT_SUM[20]), .b(INT_SUM[21]), .cin(INT_CARRY[18]),
    .sum(INT_SUM[22]), .cout(INT_CARRY[19])
  );
  assign SUM[10]   = INT_SUM[22];
  assign CARRY[10] = INT_CARRY[19];

  // -------------------------
  // bit 11
  FULL_ADDER FA16(
    .a(fpp0[11]), .b(fpp1[9]), .cin(fpp2[7]),
    .sum(INT_SUM[23]), .cout(INT_CARRY[24])
  );
  FULL_ADDER FA17(
    .a(fpp3[5]), .b(fpp4[3]), .cin(INT_CARRY[20]),
    .sum(INT_SUM[24]), .cout(INT_CARRY[23])
  );
  FULL_ADDER FA18(
    .a(INT_SUM[23]), .b(INT_SUM[24]), .cin(INT_CARRY[21]),
    .sum(INT_SUM[25]), .cout(INT_CARRY[22])
  );
  assign SUM[11]   = INT_SUM[25];
  assign CARRY[11] = INT_CARRY[22];

  // -------------------------
  // bit 12
  FULL_ADDER FA19(
    .a(fpp1[10]), .b(fpp2[8]), .cin(fpp3[6]),
    .sum(INT_SUM[26]), .cout(INT_CARRY[26])
  );
  FULL_ADDER FA20(
    .a(fpp4[4]), .b(fpp5[0]), .cin(INT_CARRY[23]),
    .sum(INT_SUM[27]), .cout(INT_CARRY[25])
  );
  FULL_ADDER FA21(
    .a(INT_SUM[26]), .b(INT_SUM[27]), .cin(INT_CARRY[24]),
    .sum(INT_SUM[28]), .cout(INT_CARRY[27])
  );
  assign SUM[12]   = INT_SUM[28];
  assign CARRY[12] = INT_CARRY[27];

  // -------------------------
  // bit 13
  FULL_ADDER FA22(
    .a(fpp1[11]), .b(fpp2[9]), .cin(fpp3[7]),
    .sum(INT_SUM[29]), .cout(INT_CARRY[29])
  );
  FULL_ADDER FA23(
    .a(fpp4[5]), .b(fpp5[1]), .cin(INT_CARRY[25]),
    .sum(INT_SUM[30]), .cout(INT_CARRY[28])
  );
  FULL_ADDER FA24(
    .a(INT_SUM[29]), .b(INT_SUM[30]), .cin(INT_CARRY[26]),
    .sum(INT_SUM[31]), .cout(INT_CARRY[31])
  );
  assign SUM[13]   = INT_SUM[31];
  assign CARRY[13] = INT_CARRY[31];

  // -------------------------
  // bit 14
  FULL_ADDER FA25(
    .a(fpp2[10]), .b(fpp3[8]), .cin(fpp4[6]),
    .sum(INT_SUM[32]), .cout(INT_CARRY[32])
  );
  FULL_ADDER FA26(
    .a(fpp5[2]), .b(INT_CARRY[28]), .cin(INT_CARRY[29]),
    .sum(INT_SUM[33]), .cout(INT_CARRY[33])
  );
  FULL_ADDER FA27(
    .a(INT_SUM[32]), .b(INT_SUM[33]), .cin(INT_CARRY[27]),
    .sum(INT_SUM[34]), .cout(INT_CARRY[34])
  );
  assign SUM[14]   = INT_SUM[34];
  assign CARRY[14] = INT_CARRY[34];

  // -------------------------
  // bit 15
  FULL_ADDER FA28(
    .a(fpp2[11]), .b(fpp3[9]), .cin(fpp4[7]),
    .sum(INT_SUM[35]), .cout(INT_CARRY[35])
  );
  FULL_ADDER FA29(
    .a(fpp5[3]), .b(INT_CARRY[32]), .cin(INT_CARRY[33]),
    .sum(INT_SUM[36]), .cout(INT_CARRY[36])
  );
  FULL_ADDER FA30(
    .a(INT_SUM[35]), .b(INT_SUM[36]), .cin(INT_CARRY[31]),
    .sum(INT_SUM[37]), .cout(INT_CARRY[37])
  );
  assign SUM[15]   = INT_SUM[37];
  assign CARRY[15] = INT_CARRY[37];

  // -------------------------
  // bit 16
  FULL_ADDER FA31(
    .a(fpp3[10]), .b(fpp4[8]), .cin(fpp5[4]),
    .sum(INT_SUM[38]), .cout(INT_CARRY[38])
  );
  FULL_ADDER FA32(
    .a(INT_SUM[38]), .b(INT_CARRY[35]), .cin(INT_CARRY[36]),
    .sum(INT_SUM[39]), .cout(INT_CARRY[39])
  );
  assign SUM[16]   = INT_SUM[39];
  assign CARRY[16] = INT_CARRY[39];

  // -------------------------
  // bit 17
  FULL_ADDER FA33(
    .a(fpp3[11]), .b(fpp4[9]), .cin(fpp5[5]),
    .sum(INT_SUM[40]), .cout(INT_CARRY[40])
  );
  FULL_ADDER FA34(
    .a(INT_SUM[40]), .b(INT_CARRY[37]), .cin(INT_CARRY[38]),
    .sum(INT_SUM[41]), .cout(INT_CARRY[41])
  );
  assign SUM[17]   = INT_SUM[41];
  assign CARRY[17] = INT_CARRY[41];

  // -------------------------
  // bit 18
  FULL_ADDER FA35(
    .a(fpp4[10]), .b(fpp5[6]), .cin(INT_CARRY[39]),
    .sum(INT_SUM[42]), .cout(INT_CARRY[42])
  );
  HALF_ADDER HA6(
    .a(INT_SUM[42]), .b(INT_CARRY[40]),
    .sum(INT_SUM[43]), .cout(INT_CARRY[43])
  );
  assign SUM[18]   = INT_SUM[43];
  assign CARRY[18] = INT_CARRY[43];

  // -------------------------
  // bit 19
  FULL_ADDER FA36(
    .a(fpp4[11]), .b(fpp5[7]), .cin(INT_CARRY[41]),
    .sum(INT_SUM[44]), .cout(INT_CARRY[44])
  );
  HALF_ADDER HA7(
    .a(INT_SUM[44]), .b(INT_CARRY[42]),
    .sum(INT_SUM[45]), .cout(INT_CARRY[45])
  );
  assign SUM[19]   = INT_SUM[45];
  assign CARRY[19] = INT_CARRY[45];

  // -------------------------
  // bit 20
  FULL_ADDER FA37(
    .a(fpp5[8]), .b(INT_CARRY[44]), .cin(1'b0),
    .sum(INT_SUM[46]), .cout(INT_CARRY[46])
  );
  HALF_ADDER HA8(
    .a(INT_SUM[46]), .b(INT_CARRY[43]),
    .sum(INT_SUM[47]), .cout(INT_CARRY[47])
  );
  assign SUM[20]   = INT_SUM[47];
  assign CARRY[20] = INT_CARRY[47];

  // -------------------------
  // bit 21
  FULL_ADDER FA38(
    .a(fpp5[9]), .b(INT_CARRY[45]), .cin(INT_CARRY[46]),
    .sum(INT_SUM[48]), .cout(INT_CARRY[48])
  );
  HALF_ADDER HA9(
    .a(INT_SUM[48]), .b(fpp5[10]),
    .sum(INT_SUM[49]), .cout(INT_CARRY[49])
  );
  HALF_ADDER HA10(
    .a(INT_SUM[49]), .b(fpp5[11]),
    .sum(INT_SUM[50]), .cout(INT_CARRY[50])
  );
  assign SUM[21]   = INT_SUM[50];
  assign CARRY[21] = INT_CARRY[50];

//=============================
// 최종 출력
//=============================
assign sum   = SUM;
assign carry = CARRY;

endmodule


/******************** Booth Encoder ********************/
module booth_encoder (x, single, double, neg, pzero,nzero);

input [2:0] x;

output      single;
output      double;
output      neg;
output      pzero;
output      nzero;

// Radix-4 Booth : x = {x[2], x[1], x[0]}
wire  w0 = ~(x[1] ^ x[2]);
wire  w1 =  (x[0] ^ x[1]);

assign single = x[0] ^ x[1];
assign neg    = x[2];
assign double = ~(w0 | w1);

// zero check
assign pzero = ~x[0] & ~x[1] & ~x[2];	// 000
assign nzero =  x[0] &  x[1] &  x[2];	// 111

endmodule

/******************** Booth Selector ********************/
module booth_selector (double, shifted, single, y, neg, p);

input double;
input shifted;
input single;
input y;
input neg;

output p;

assign  p = (neg ^ ((y & single) | (shifted & double)));

endmodule

/******************** 1bit Full Adder ********************/

module FULL_ADDER ( a, b, cin, sum, cout );

input  a;

input  b;

input  cin;

output sum;

output cout;

   wire TMP;

   assign TMP = a ^ b;

   assign sum = TMP ^ cin;

   assign cout =  ~ (( ~ (TMP & cin)) & ( ~ (a & b)));

endmodule
 
module HALF_ADDER ( a, b, sum, cout );

input  a;

input  b;

output sum;

output cout;

   assign sum = a ^ b;

   assign cout = a & b;

endmodule
