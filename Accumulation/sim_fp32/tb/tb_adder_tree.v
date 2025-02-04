`timescale 1ns/1ps

module tb_adder_tree();

  localparam N_INPUT     = 4;
  localparam OP_WIDTH    = 4;
  localparam N_STAGE     = $clog2(N_INPUT);
  localparam INPUT_WIDTH = N_INPUT*OP_WIDTH;
  localparam OUTPUT_WIDTH = OP_WIDTH + N_STAGE;

  reg [OP_WIDTH-1:0] op[N_INPUT-1:0];

  wire  [INPUT_WIDTH-1:0] data;
  wire [OUTPUT_WIDTH-1:0] out;

  BADA_adder_tree adder_tree(
    .i_data(data),
    .o_data(out)
  );

  genvar i;
  for(i=0; i<N_INPUT; i++)
    assign data[OP_WIDTH*(i+1):OP_WIDTH*i] = op[i];

  initial begin 
    //Dump .fsdb
    $fsdbDumpfile("waveform.fsdb");
    $fsdbDumpvars(0, tb_adder_tree, "+all");
    
    //Dump .vcd
    //$dumpfile("waveform.vcd");
    //$dumpvars(0, tb_adder_tree);
    //$dumpvars(0, tb_adder_tree.adder_tree);
  end

  initial begin
    $display($stime, "\t", "Siumulation START");
    op[0] <= 1;
    op[1] <= 1;
    op[2] <= 1;
    op[3] <= 1;
    $display($stime, "\t", "Siumulation FINISH");
    $finish;
  end

endmodule
