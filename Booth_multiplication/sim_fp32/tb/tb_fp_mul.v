`timescale 1ns/1ps

module tb_fp_mul;

localparam  CLK_PERIOD    = 4;
localparam  DWIDTH        = 32;

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


fp32_mul #(
  .DWIDTH   (32 ),
  .EWIDTH   (8  ),
  .MWIDTH   (23 ),
	.BIAS     (127)
) u_fp32_mul(
	    .a_operand 	  (a_operand   // i [DWIDTH-1:0]
	),  .b_operand 	  (b_operand   // i [DWIDTH-1:0]
	),  .result    	  (result      // o [DWIDTH-1:0]
	),  .Exception 	  (Exception   // o         
	),  .Overflow  	  (Overflow    // o         
	),  .Underflow 	  (Underflow   // o         
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
  $fsdbDumpvars(0, tb_fp_mul, "+all");
  
  //Dump .vcd
  //$dumpfile("waveform.vcd");
  //$dumpvars(0, tb_bada);
  //$dumpvars(0, tb_bada.u_BADA_array);
end

initial begin
  data_x[0] = 32'b0_10000101_111_0001_1000_0000_0000_0000;
  data_y[0] = 32'b1_10000010_110_0100_0000_0000_0000_0000;
  data_o[0] = 32'b1_10001001_101_0111_0001_0110_0000_0000;

  data_x[1] = 32'b0_10000111_111_0001_1001_0000_0000_0000;
  data_y[1] = 32'b0_10100111_111_0001_1001_1000_0000_0000;
  data_o[1] = 32'b0_10110000_110_0011_1111_0111_1111_1110;

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
