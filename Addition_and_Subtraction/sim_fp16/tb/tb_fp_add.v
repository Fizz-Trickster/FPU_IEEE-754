`timescale 1ns/1ps

module tb_fp_add;

localparam  CLK_PERIOD    = 4;
localparam  DWIDTH        = 16;

reg                       clk;
reg                       rstn;

always #(CLK_PERIOD/2) clk = ~clk;

reg   [DWIDTH-1:0]  a_operand;
reg   [DWIDTH-1:0]  b_operand;

wire  [DWIDTH-1:0]  result;
wire                Exception;
wire                Overflow;
wire                Underflow;

reg  [9:0][DWIDTH-1:0] data_x ;
reg  [9:0][DWIDTH-1:0] data_y ;
reg  [9:0][DWIDTH-1:0] data_o ;


fp16_add #(
  .DWIDTH   (16 ),
  .EWIDTH   (5  ),
  .MWIDTH   (10 ),
  .RWIDTH   (3  )
) u_fp16_add(
	    .a_operand 	  (a_operand   // i [DWIDTH-1:0]
	),  .b_operand 	  (b_operand   // i [DWIDTH-1:0]
	),  .result    	  (result      // o [DWIDTH-1:0]
	),  .Exception 	  (Exception   // o         
  ));

integer  idx = 0;
// assertion 수정
reg result_valid;
always @(posedge clk or negedge rstn) begin
  if (!rstn)
    result_valid <= 0;
  else if ($stable(result))
    result_valid <= 1;
end

property check_result;
  @(posedge clk) disable iff (!rstn)
  result_valid |-> (result === data_o[idx]);
endproperty

assert_result: assert property(check_result)
  else begin
    $display("Error: Result mismatch at time %0t!", $time);
    $display("idx     : %d", idx);
    $display("Expected: %b", data_o[idx]);
    $display("Got     : %b", result);
    $finish;
  end

initial begin 
  //Dump .fsdb
  $fsdbDumpfile("waveform.fsdb");
  $fsdbDumpvars(0, tb_fp_add, "+all");
  
  //Dump .vcd
  //$dumpfile("waveform.vcd");
  //$dumpvars(0, tb_bada);
  //$dumpvars(0, tb_bada.u_BADA_array);
end

initial begin
  // Add + Common case
  data_x[0] = 16'b0_10101_11_0001_1001;
  data_y[0] = 16'b0_10001_11_0100_0001;
  data_o[0] = 16'b0_10101_11_1000_1101;

  // Add + Normalize case
  data_x[1] = 16'b0_10101_11_0001_1001;
  data_y[1] = 16'b0_10010_11_0100_0001;
  data_o[1] = 16'b0_10110_00_0000_0001;

  // Subtract + Normalize case
  data_x[2] = 16'b0_10101_11_0001_1001;
  data_y[2] = 16'b1_10001_11_0100_0001;
  data_o[2] = 16'b0_10101_11_1000_1101;
  
  // Subtract + Common case
  data_x[3] = 16'b1_10101_11_0001_1001;
  data_y[3] = 16'b0_10010_11_0100_0001;
  data_o[3] = 16'b1_10101_10_1010_0101;

  $display($stime, "\t", "Simulation START");
  clk   <= 1;
  rstn  <= 1;

  a_operand <= 0;
  b_operand <= 0;

  repeat (1) @(negedge clk); rstn   <= 0;
  repeat (3) @(negedge clk); rstn   <= 1;
  
  a_operand <= data_x[idx];
  b_operand <= data_y[idx];
  repeat(5) @(posedge clk);
  idx = idx + 1;

  a_operand <= data_x[idx];
  b_operand <= data_y[idx];
  repeat(5) @(posedge clk);

  repeat(96) @(posedge clk);
  $display($stime, "\t", "Simulation FINISH");
  $finish;
end

endmodule
