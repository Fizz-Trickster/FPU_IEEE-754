module radix4_booth_multiplier #(
  parameter DWIDTH = 16
)(
  input     [1*DWIDTH-1:0] op_a_dat,        // 11-bit multiplier
  input     [1*DWIDTH-1:0] op_b_dat,        // 11-bit multiplicand
  output    [2*DWIDTH-1:0] sum,             // 22-bit sum (output)
  output    [2*DWIDTH-1:0] carry            // 22-bit carry (output)
);

// Booth encoding stage
wire    [23:0] pp_out_l0n0_0;
wire    [23:0] pp_out_l0n0_1;
wire    [23:0] pp_out_l0n1_0;
wire    [23:0] pp_out_l0n1_1;
wire    [31:0] pp_out_l1n0_0;
wire    [31:0] pp_out_l1n0_1;

wire    [16:0] sel_data_0;
wire    [16:0] sel_data_1;
wire    [16:0] sel_data_2;
wire    [16:0] sel_data_3;
wire    [16:0] sel_data_4;
wire    [16:0] sel_data_5;
wire    [16:0] sel_data_6;
wire    [16:0] sel_data_7;
wire           sel_inv_0;
wire           sel_inv_1;
wire           sel_inv_2;
wire           sel_inv_3;
wire           sel_inv_4;
wire           sel_inv_5;
wire           sel_inv_6;
wire           sel_inv_7;

reg      [2:0] code_0;
reg      [2:0] code_1;
reg      [2:0] code_2;
reg      [2:0] code_3;
reg      [2:0] code_4;
reg      [2:0] code_5;
reg      [2:0] code_6;
reg      [2:0] code_7;
reg      [8:0] code_hi;
reg      [8:0] code_lo;
reg            fp16_sign;

reg     [15:0] op_a_cur_dat;
reg     [15:0] op_b_cur_dat;

reg     [23:0] ppre_0;
reg     [23:0] ppre_1;
reg     [23:0] ppre_2;
reg     [23:0] ppre_3;
reg     [23:0] ppre_4;
reg     [23:0] ppre_5;
reg     [23:0] ppre_6;
reg     [23:0] ppre_7;
reg     [23:0] ppre_8;
reg     [23:0] ppre_9;

reg    [119:0] pp_in_l0n0;
reg    [119:0] pp_in_l0n1;
reg    [127:0] pp_in_l1n0;

reg     [15:0] src_data_0;
reg     [15:0] src_data_1;

always @(
 op_a_dat
 or op_b_dat
 ) begin
    op_a_cur_dat = op_a_dat[15:0];
    op_b_cur_dat = op_b_dat[15:0];
end
  
//==========================================================
// Booth recoding and selection, radix-4
//==========================================================

always @(
  op_a_cur_dat
  ) begin
    code_lo = {op_a_cur_dat[7:0], 1'b0};
end

always @(
  op_a_cur_dat
  ) begin
    code_hi = op_a_cur_dat[15:7];
              
end

always @(
  code_lo
  ) begin
    code_0 = code_lo[2:0];
    code_1 = code_lo[4:2];
    code_2 = code_lo[6:4];
    code_3 = code_lo[8:6];
end

always @(
  code_hi
  ) begin
    code_4 = code_hi[2:0];
    code_5 = code_hi[4:2];
    code_6 = code_hi[6:4];
    code_7 = code_hi[8:6];
end

always @(
  op_b_cur_dat
  ) begin
    src_data_0 = op_b_cur_dat;
    src_data_1 = op_b_cur_dat;
end

//always @(
//  op_a_dat
//  or op_b_dat
//  ) begin
//    fp16_sign = (op_a_dat[15] ^ op_b_dat[15]);
//end

NV_NVDLA_CMAC_CORE_MAC_booth u_booth_0 (
   .code     (code_0[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_0[15:0])    //|< r
  ,.out_data (sel_data_0[16:0])    //|> w
  ,.out_inv  (sel_inv_0)           //|> w
  );

NV_NVDLA_CMAC_CORE_MAC_booth u_booth_1 (
   .code     (code_1[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_0[15:0])    //|< r
  ,.out_data (sel_data_1[16:0])    //|> w
  ,.out_inv  (sel_inv_1)           //|> w
  );


NV_NVDLA_CMAC_CORE_MAC_booth u_booth_2 (
   .code     (code_2[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_0[15:0])    //|< r
  ,.out_data (sel_data_2[16:0])    //|> w
  ,.out_inv  (sel_inv_2)           //|> w
  );


NV_NVDLA_CMAC_CORE_MAC_booth u_booth_3 (
   .code     (code_3[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_0[15:0])    //|< r
  ,.out_data (sel_data_3[16:0])    //|> w
  ,.out_inv  (sel_inv_3)           //|> w
  );


NV_NVDLA_CMAC_CORE_MAC_booth u_booth_4 (
   .code     (code_4[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_1[15:0])    //|< r
  ,.out_data (sel_data_4[16:0])    //|> w
  ,.out_inv  (sel_inv_4)           //|> w
  );

NV_NVDLA_CMAC_CORE_MAC_booth u_booth_5 (
   .code     (code_5[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_1[15:0])    //|< r
  ,.out_data (sel_data_5[16:0])    //|> w
  ,.out_inv  (sel_inv_5)           //|> w
  );


NV_NVDLA_CMAC_CORE_MAC_booth u_booth_6 (
   .code     (code_6[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_1[15:0])    //|< r
  ,.out_data (sel_data_6[16:0])    //|> w
  ,.out_inv  (sel_inv_6)           //|> w
  );


NV_NVDLA_CMAC_CORE_MAC_booth u_booth_7 (
   .code     (code_7[2:0])         //|< r
  ,.is_8bit  (1'b0)                //|< r
  ,.sign     (1'b0)                //|< r
  ,.src_data (src_data_1[15:0])    //|< r
  ,.out_data (sel_data_7[16:0])    //|> w
  ,.out_inv  (sel_inv_7)           //|> w
  );

//==========================================================
// CSA tree input
//==========================================================

always @(
  sel_data_0
  or sel_data_1
  or sel_inv_0
  or sel_data_2
  or sel_inv_1
  or sel_data_3
  or sel_inv_2
  or sel_inv_3
  ) begin
    ppre_0 = {7'b0, sel_data_0};
    ppre_1 = {5'b0, sel_data_1, 1'b0, sel_inv_0};
    ppre_2 = {3'b0, sel_data_2, 1'b0, sel_inv_1, 2'b0};
    ppre_3 = {1'b0, sel_data_3, 1'b0, sel_inv_2, 4'b0};
    ppre_4 = {17'b0, sel_inv_3, 6'b0};
end

always @(
  sel_data_4
  or sel_data_5
  or sel_inv_4
  or sel_data_6
  or sel_inv_5
  or sel_data_7
  or sel_inv_6
  or sel_inv_7
  ) begin
    ppre_5 = {7'b0, sel_data_4};
    ppre_6 = {5'b0, sel_data_5, 1'b0, sel_inv_4};
    ppre_7 = {3'b0, sel_data_6, 1'b0, sel_inv_5, 2'b0};
    ppre_8 = {1'b0, sel_data_7, 1'b0, sel_inv_6, 4'b0};
    ppre_9 = {17'b0, sel_inv_7, 6'b0};
end

//==========================================================
// CSA tree level 1
//==========================================================

always @(
  ppre_4
  or ppre_3
  or ppre_2
  or ppre_1
  or ppre_0
  ) begin
    pp_in_l0n0 = {ppre_4, ppre_3, ppre_2, ppre_1, ppre_0};
end

always @(
  ppre_9
  or ppre_8
  or ppre_7
  or ppre_6
  or ppre_5
  ) begin
    pp_in_l0n1 = {ppre_9, ppre_8, ppre_7, ppre_6, ppre_5};
end

NV_DW02_tree #(5, 24) u_tree_l0n0 (
   .INPUT    (pp_in_l0n0[119:0])   //|< r
  ,.OUT0     (pp_out_l0n0_0[23:0]) //|> w
  ,.OUT1     (pp_out_l0n0_1[23:0]) //|> w
  );

NV_DW02_tree #(5, 24) u_tree_l0n1 (
   .INPUT    (pp_in_l0n1[119:0])   //|< r
  ,.OUT0     (pp_out_l0n1_0[23:0]) //|> w
  ,.OUT1     (pp_out_l0n1_1[23:0]) //|> w
  );

//==========================================================
// CSA tree level 2
//==========================================================
always @(
  pp_out_l0n1_1
  or pp_out_l0n1_0
  or pp_out_l0n0_1
  or pp_out_l0n0_0
  ) begin
    pp_in_l1n0 = {{pp_out_l0n1_1, 8'b0},
                  {pp_out_l0n1_0, 8'b0},
                  {8'b0, pp_out_l0n0_1},
                  {8'b0, pp_out_l0n0_0}};
end

NV_DW02_tree #(4, 32) u_tree_l1n0 (
   .INPUT    (pp_in_l1n0[127:0])   //|< r
  ,.OUT0     (pp_out_l1n0_0[31:0]) //|> w
  ,.OUT1     (pp_out_l1n0_1[31:0]) //|> w
  );

assign  sum   = pp_out_l1n0_0;
assign  carry = pp_out_l1n0_1;

endmodule
