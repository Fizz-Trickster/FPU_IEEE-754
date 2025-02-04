`timescale 1ns/1ps

module tb_bada;

localparam  CLK_PERIOD    = 4;
localparam  DATA_WIDTH    = 8;
localparam  INST_WIDTH    = 32;
//localparam  INPUT_WIDTH   = 2*16*02;   // 01B
localparam  INPUT_WIDTH   = 2*16*04;   // 02B
//localparam  INPUT_WIDTH   = 2*16*08;   // 04B
//localparam  INPUT_WIDTH   = 2*16*16;   // 08B
//localparam  INPUT_WIDTH   = 2*16*32;   // 16B
localparam  OUTPUT_WIDTH  = 4*16*20;
localparam  MAC_LATENCY   = 4;          // NBC_BUF_IN / NBC_BUF_OUT

reg                       clk;
reg                       rstn;

wire  [OUTPUT_WIDTH-1:0]  out;

always #(CLK_PERIOD/2) clk = ~clk;

reg [DATA_WIDTH -1:0] cnt;
reg [INPUT_WIDTH-1:0] act;
reg [INPUT_WIDTH-1:0] weight;
reg                   data_en;

always @(posedge clk, negedge rstn) begin
  if (!rstn) begin
    cnt     <= 'd0;
    act     <= 'd0;
    weight  <= 'd0;
    data_en <= 'd0;
  end else if(cnt==0) begin
    data_en <= 'd1;
    cnt     <= cnt + 'd1;
    //act     <= {128{cnt>>2}};
    //weight  <= {INPUT_WIDTH{8'd1}};
    for(int i=0;i<32;i++) act[8*i+:8] <= i;
    weight  <= {INPUT_WIDTH/8{8'd1}};
  end else begin
    data_en <= 'd0;
    //if(cnt==4*MAC_LATENCY+4-1) 
    if(cnt==(4*MAC_LATENCY+4)/2-1) 
      cnt <='d0;
    else          
      cnt <= cnt + 'd1;
  end
end

wire [INST_WIDTH-1:0] inst;

inst_ctrl #(
  .INST_WIDTH   (INST_WIDTH),
  .MAC_LATENCY  (MAC_LATENCY)
) u_inst_ctrl(
      .clk     (clk          // i                
  ),  .rstn    (rstn         // i                
  ),  .data_en (data_en      // i                
  ),  .inst    (inst         // o [31:0]
  ));


BADA_array u_BADA_array(
      .clk      (clk        // i
  ),  .reset    (rstn       // i
  ),  .inst     (inst       // i [  31:0]
  ),  .idata    (act        // i [ 255:0]
  ),  .wdata    (weight     // i [ 255:0]
  ),  .odata    (out        // o [1279:0]
  ));

initial begin 
  //Dump .fsdb
  $fsdbDumpfile("waveform.fsdb");
  $fsdbDumpvars(0, tb_bada, "+all");
  
  //Dump .vcd
  //$dumpfile("waveform.vcd");
  //$dumpvars(0, tb_bada);
  //$dumpvars(0, tb_bada.u_BADA_array);
end

initial begin
  $display($stime, "\t", "Siumulation START");
  clk   <= 1;
  rstn  <= 1;
  repeat (1) @(negedge clk); rstn   <= 0;
  repeat (3) @(negedge clk); rstn   <= 1;
  
  //repeat(16) @(posedge clk);
  repeat(96) @(posedge clk);
  $display($stime, "\t", "Siumulation FINISH");
  $finish;
end

endmodule
