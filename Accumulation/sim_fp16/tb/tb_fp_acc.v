`timescale 1ns/1ps

module tb_fp_acc;

localparam  CLK_PERIOD    = 4;
localparam  DWIDTH        = 16;

reg                       clk;
reg                       rstn;

always #(CLK_PERIOD/2) clk = ~clk;

reg   [DWIDTH-1:0]  a_operand;
reg   [DWIDTH-1:0]  b_operand;

wire  [DWIDTH-1:0]  result;
wire                valid_out;
wire                Overflow;
wire                Underflow;

reg  [9:0][DWIDTH-1:0] data_x ;
reg  [9:0][DWIDTH-1:0] data_y ;
reg  [9:0][DWIDTH-1:0] data_o ;


kulisch_acc_fp16 #(
  .DWIDTH ( 16 ),
  .EWIDTH ( 5  ),
  .MWIDTH ( 10 ),
  .BIAS   ( 15 ),
  .WWIDTH ( 79 ),
  .VWIDTH ( 12 ) 
) u_kulisch_acc_fp16(
	    .clk            (clk   
	),  .rst_n          (rstn      
	),  .i_fp_data      (a_operand   // i [DWIDTH-1:0]
	),  .i_init_acc     (0   
	),  .i_init         (0
	),  .o_kulisch_acc  (result
  ));

integer  idx = 0;
//// assertion 수정
//reg result_valid;
//always @(posedge clk or negedge rstn) begin
//  if (!rstn)
//    result_valid <= 0;
//  else if ($stable(result))
//    result_valid <= 1;
//end
//
//property check_result;
//  @(posedge clk) disable iff (!rstn)
//  result_valid |-> (result === data_o[idx]);
//endproperty
//
//assert_result: assert property(check_result)
//  else begin
//    $display("Error: Result mismatch at time %0t!", $time);
//    $display("idx     : %d", idx);
//    $display("Expected: %b", data_o[idx]);
//    $display("Got     : %b", result);
//    $finish;
//  end

initial begin 
  //Dump .fsdb
  $fsdbDumpfile("waveform.fsdb");
  $fsdbDumpvars(0, tb_fp_acc, "+all");
  $fsdbDumpvars(0, tb_fp_acc, "+functions");
  
  //Dump .vcd
  //$dumpfile("waveform.vcd");
  //$dumpvars(0, tb_bada);
  //$dumpvars(0, tb_bada.u_BADA_array);
end

initial begin
  // one 
  data_x[0] = 16'b0_01111_00_0000_0000;
  data_y[0] = 16'b0_11010_10_0111_0101;
  data_o[0] = 16'b0_11010_10_0111_1001;

  // smallest positive subnormal number
  data_x[1] = 16'b0_00000_00_0000_0001;
  data_y[1] = 16'b0_11010_10_0111_0101;
  data_o[1] = 16'b0_11010_10_0111_1001;

  // largest positive subnormal number
  data_x[2] = 16'b0_00000_11_1111_1111;
  data_y[2] = 16'b0_11010_10_0111_0101;
  data_o[2] = 16'b0_11010_10_0111_1001;

  // largest normal number
  data_x[3] = 16'b0_11110_11_1111_1111;
  data_y[3] = 16'b0_11010_10_0111_0101;
  data_o[3] = 16'b0_11010_10_0111_1001;

  $display($stime, "\t", "Simulation START");
  clk   <= 1;
  rstn  <= 1;

  a_operand <= 0;
  b_operand <= 0;

  repeat (1) @(negedge clk); rstn   <= 0;
  repeat (3) @(negedge clk); rstn   <= 1;
  
  a_operand <= data_x[idx];
  b_operand <= data_y[idx];
  repeat(1) @(negedge clk);
  idx = idx + 1;

  a_operand <= data_x[idx];
  b_operand <= data_y[idx];
  repeat(1) @(negedge clk);
  idx = idx + 1;

  a_operand <= data_x[idx];
  b_operand <= data_y[idx];
  repeat(1) @(negedge clk);
  idx = idx + 1;

  a_operand <= data_x[idx];
  b_operand <= data_y[idx];
  repeat(1) @(negedge clk);
  idx = idx + 1;

  a_operand <= 'd0; 
  b_operand <= 'd0; 
  repeat(1) @(negedge clk);
  idx = idx + 1;

  repeat(96) @(posedge clk);
  $display($stime, "\t", "Simulation FINISH");
  $finish;
end

endmodule
