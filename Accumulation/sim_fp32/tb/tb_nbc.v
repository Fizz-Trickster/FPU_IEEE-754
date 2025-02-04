`timescale 1ns/1ps

module tb_nbc();

  localparam OP_WIDTH    = 4;
  localparam N_INPUT     = 4;
  localparam INPUT_WIDTH = N_INPUT*(2*OP_WIDTH);

  reg [OP_WIDTH-1:0] op_a[N_INPUT-1:0];
  reg [OP_WIDTH-1:0] op_b[N_INPUT-1:0];

  wire [INPUT_WIDTH-1:0] op_a_concat;
  wire [INPUT_WIDTH-1:0] op_b_concat;

  wire [INPUT_WIDTH-1:0] res_a_concat;
  wire [INPUT_WIDTH-1:0] res_b_concat;

  wire [OP_WIDTH-1:0] res_a[N_INPUT-1:0];
  wire [OP_WIDTH-1:0] res_b[N_INPUT-1:0];

  genvar i;
  generate
  for(i=0; i<N_INPUT; i=i+1) begin: gen_concat
    assign op_a_concat[OP_WIDTH*(i+1)-1:OP_WIDTH*i] = op_a[i];
    assign op_b_concat[OP_WIDTH*(i+1)-1:OP_WIDTH*i] = op_b[i];

    assign res_a[i] = res_a_concat[OP_WIDTH*(i+1)-1:OP_WIDTH*i];
    assign res_b[i] = res_b_concat[OP_WIDTH*(i+1)-1:OP_WIDTH*i];
  end
  endgenerate

  BADA_nbc #(
    .OP_WIDTH(OP_WIDTH),
    .INPUT_WIDTH(INPUT_WIDTH)
  ) nbc(
    .op_a(op_a_concat),
    .op_b(op_b_concat),
    .res_a(res_a_concat),
    .res_b(res_b_concat)
  );

  reg clock;

  always begin
    #5 clock = ~clock;
  end

  initial begin 
    //Dump .fsdb
    $fsdbDumpfile("waveform.fsdb");
    $fsdbDumpvars(0, tb_nbc, "+all");
    
    //Dump .vcd
    //$dumpfile("waveform.vcd");
    //$dumpvars(0, tb_nbc);
    //$dumpvars(0, tb_nbc.nbc);
  end

  initial begin
    clock = 0;

    op_a[0] <= 4'd0;
    op_a[1] <= 4'd0;
    op_a[2] <= 4'd0;
    op_a[3] <= 4'd0;

    op_b[0] <= 4'd0;
    op_b[1] <= 4'd0;
    op_b[2] <= 4'd0;
    op_b[3] <= 4'd0;

    $display($stime, "\t", "Siumulation START");
    #10
    op_a[0] <= 4'd1;
    op_a[1] <= 4'd0;
    op_a[2] <= 4'd2;
    op_a[3] <= 4'd0;

    op_b[0] <= 4'd3;
    op_b[1] <= 4'd0;
    op_b[2] <= 4'd4;
    op_b[3] <= 4'd0;
    #10

    $display($stime, "\t", "Siumulation FINISH");
    $finish;
  end

endmodule
