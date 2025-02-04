`timescale 1ns/1ps

module tb_tensor_core;

localparam  CLK_PERIOD    = 4;
localparam  DWIDTH        = 16;
localparam  AWIDTH        = 91;

reg                       clk;
reg                       rstn;

always #(CLK_PERIOD/2) clk = ~clk;

reg   [0:3][0:3][DWIDTH-1:0]  a_operand;
reg   [0:3][0:3][DWIDTH-1:0]  b_operand;

wire  [DWIDTH-1:0]  result;
wire                valid_out;
wire                Overflow;
wire                Underflow;

reg  [9:0][0:3][0:3][DWIDTH-1:0] data_x ;
reg  [9:0][0:3][0:3][DWIDTH-1:0] data_y ;
reg  [9:0][0:3][0:3][DWIDTH-1:0] data_o ;


tensor_core_top #(
  .DWIDTH ( DWIDTH ),
  .AWIDTH ( AWIDTH ) 
) u_tensor_core_top(
	    .clk            (clk   
	),  .rst_n          (rstn      
	),  .A_in           (a_operand   // i [DWIDTH-1:0]
	),  .B_in           (b_operand   // i [DWIDTH-1:0]   
	),  .in_valid       (0
	),  .C_in           (0           // i [DWIDTH-1:0]   
	),  .C_in_valid     (0
	),  .C_out          (            // i [DWIDTH-1:0]   
	),  .out_valid      ( 
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
  $fsdbDumpvars(0, tb_tensor_core, "+all");
  $fsdbDumpvars(0, tb_tensor_core, "+functions");
  
  //Dump .vcd
  //$dumpfile("waveform.vcd");
  //$dumpvars(0, tb_bada);
  //$dumpvars(0, tb_bada.u_BADA_array);
end

initial begin
  // one 
  data_x[0] = {16'(4*0+0), 16'(4*0+1), 16'(4*0+2), 16'(4*0+3), 
               16'(4*1+0), 16'(4*1+1), 16'(4*1+2), 16'(4*1+3), 
               16'(4*2+0), 16'(4*2+1), 16'(4*2+2), 16'(4*2+3), 
               16'(4*3+0), 16'(4*3+1), 16'(4*3+2), 16'(4*3+3)}; 

  data_y[0] = {16'(4*0+0), 16'(4*0+1), 16'(4*0+2), 16'(4*0+3), 
               16'(4*1+0), 16'(4*1+1), 16'(4*1+2), 16'(4*1+3), 
               16'(4*2+0), 16'(4*2+1), 16'(4*2+2), 16'(4*2+3), 
               16'(4*3+0), 16'(4*3+1), 16'(4*3+2), 16'(4*3+3)}; 

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

  //a_operand <= data_x[idx];
  //b_operand <= data_y[idx];
  //repeat(1) @(negedge clk);
  //idx = idx + 1;

  //a_operand <= data_x[idx];
  //b_operand <= data_y[idx];
  //repeat(1) @(negedge clk);
  //idx = idx + 1;

  //a_operand <= data_x[idx];
  //b_operand <= data_y[idx];
  //repeat(1) @(negedge clk);
  //idx = idx + 1;

  //a_operand <= 'd0; 
  //b_operand <= 'd0; 
  //repeat(1) @(negedge clk);
  //idx = idx + 1;

  repeat(96) @(posedge clk);
  $display($stime, "\t", "Simulation FINISH");
  $finish;
end

endmodule
