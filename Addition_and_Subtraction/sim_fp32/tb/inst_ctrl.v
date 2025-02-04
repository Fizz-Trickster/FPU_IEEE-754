`timescale 1ns/1ps

`ifdef GATESIM
  `define delay 1
`else
  `define delay 0
`endif

module inst_ctrl #(
  parameter INST_WIDTH  = 32,
  parameter MAC_LATENCY = 4       // NBC_BUF_IN / NBC_BUF_OUT
)(
  input clk,
  input rstn,
  input data_en,
  output [INST_WIDTH-1:0] inst
);

typedef enum logic[3:0] {
  S_IDLE,
  S_BUF_RD,       // IBUF, WBUF Read
  S_BSU,
  //S_BSU_BUF_RD, // Not Used
  S_IM_WM,        // Input MSB - Weight MSB
  S_IM_WL,        // Input MSB - Weight LSB
  S_IL_WM,        // Input LSB - Weight MSB
  S_IL_WL,        // Input LSB - Weight LSB
  S_START
} state_t;

state_t cur_state, nxt_state;

reg [3:0] macLatency; 
reg [3:0] macLatency_d; 

always @(posedge clk, negedge rstn) begin
  if (!rstn) begin
    cur_state <= S_IDLE;
  end else begin
    cur_state <= nxt_state;
  end
end

always @(*) begin
  nxt_state = cur_state; // default 
  case (cur_state)
    S_IDLE        : if(data_en            )         nxt_state = S_BUF_RD;              
    S_BUF_RD      :                                 nxt_state = S_BSU;        // 1 clk             
    S_BSU         :                                 nxt_state = S_IM_WM;      // 1 clk         
    //S_BSU_BUF_RD  :                                 nxt_state = S_IM_WM;    // 1 clk         
    S_IM_WM       : if(macLatency == MAC_LATENCY-1) nxt_state = S_IM_WL;      // (MAC_LATENCY) clk         
    S_IM_WL       : if(macLatency == MAC_LATENCY-1) nxt_state = S_IL_WM;      // (MAC_LATENCY) clk         
    S_IL_WM       : if(macLatency == MAC_LATENCY-1) nxt_state = S_IL_WL;      // (MAC_LATENCY) clk         
    S_IL_WL       : if(macLatency == MAC_LATENCY-1) nxt_state = S_START;      // (MAC_LATENCY) clk         
    S_START       :                                 nxt_state = S_BUF_RD;     // 
  endcase
end

// ===============================================================
// IBUF, WBUF Control
// ===============================================================
wire        buf_CSB = !(data_en ||                // Write
                        cur_state == S_BUF_RD);   // Read
wire        buf_WEB = !(data_en);                 // Write 

reg   [5:0] buf_wrADDR;
reg   [5:0] buf_rdADDR;

always @(posedge clk, negedge rstn) begin
  if (!rstn) begin
    buf_wrADDR  <= 6'd0;              // i/wbuf wrADDR            
  end else if(!buf_WEB)begin
    buf_wrADDR  <= buf_wrADDR + 1'd1; // i/wbuf wrADDR            
  end
end

always @(posedge clk, negedge rstn) begin
  if (!rstn) begin
    buf_rdADDR  <= 6'd0;              // i/wbuf rdADDR            
  end else if(!buf_CSB && buf_WEB)begin
    buf_rdADDR  <= buf_rdADDR + 1'd1; // i/wbuf rdADDR            
  end
end

wire  [5:0] buf_ADDR = (!buf_WEB) ? buf_wrADDR : buf_rdADDR ;

assign #(`delay) inst[08:08] = buf_CSB;
assign #(`delay) inst[07:07] = buf_WEB;
assign #(`delay) inst[05:00] = buf_ADDR;

// ===============================================================
// HOB(64Bx2), LOB(64Bx2) Control
// ===============================================================
//wire        bsu_buf_CSB = !(cur_state == S_BSU || cur_state == S_BSU_BUF_RD);
//wire        bsu_buf_WEB = !(cur_state == S_BSU);
//
//reg   [3:0] bsu_buf_wrADDR;
//reg   [3:0] bsu_buf_rdADDR;
//
//always @(posedge clk, negedge rstn) begin
//  if (!rstn) begin
//    bsu_buf_wrADDR  <= 4'd0;              // i/wbuf wrADDR            
//  end else if(!bsu_buf_WEB)begin
//    bsu_buf_wrADDR  <= bsu_buf_wrADDR + 1'd1; // i/wbuf wrADDR            
//  end
//end
//
//always @(posedge clk, negedge rstn) begin
//  if (!rstn) begin
//    bsu_buf_rdADDR  <= 4'd0;              // i/wbuf rdADDR            
//  end else if(!bsu_buf_CSB && bsu_buf_WEB)begin
//    bsu_buf_rdADDR  <= bsu_buf_rdADDR + 1'd1; // i/wbuf rdADDR            
//  end
//end
//
//wire  [3:0] bsu_buf_ADDR = (!bsu_buf_WEB) ? bsu_buf_wrADDR : bsu_buf_rdADDR ;
//
//assign inst[15:15] = bsu_buf_CSB;
//assign inst[14:14] = bsu_buf_WEB;
//assign inst[13:10] = bsu_buf_ADDR;
//assign inst[16:16] = (cur_state == S_IM_WM || cur_state == S_IM_WL ) ;
//assign inst[17:17] = (cur_state == S_IM_WM || cur_state == S_IL_WM ) ;

assign #(`delay) inst[14:14] = (cur_state == S_BSU);
assign #(`delay) inst[16:16] = (cur_state == S_IM_WM || cur_state == S_IM_WL ) ;
assign #(`delay) inst[17:17] = (cur_state == S_IM_WM || cur_state == S_IL_WM ) ;
// ===============================================================
// NBC BUF(16B) Control
// ===============================================================
always @(posedge clk, negedge rstn) begin
  if (!rstn) begin
    macLatency   <= 'd0;
    macLatency_d <= 'd0;
  end else begin
    macLatency_d <= macLatency;
    case(cur_state)
      S_IM_WM : begin
        if(macLatency == MAC_LATENCY-1) macLatency <= 'd0;
        else                            macLatency <= macLatency +'d1;
      end
      S_IM_WL : begin
        if(macLatency == MAC_LATENCY-1) macLatency <= 'd0;
        else                            macLatency <= macLatency +'d1;
      end
      S_IL_WM : begin
        if(macLatency == MAC_LATENCY-1) macLatency <= 'd0;
        else                            macLatency <= macLatency +'d1;
      end
      S_IL_WL : begin
        if(macLatency == MAC_LATENCY-1) macLatency <= 'd0;
        else                            macLatency <= macLatency +'d1;
      end
    endcase
  end
end

assign #(`delay) inst[26:26] = !((cur_state == S_IM_WM ||
                                  cur_state == S_IM_WL ||
                                  cur_state == S_IL_WM ||
                                  cur_state == S_IL_WL   ) && |macLatency);

assign #(`delay) inst[25:25] = !((cur_state == S_IM_WM ||
                                  cur_state == S_IM_WL ||
                                  cur_state == S_IL_WM ||
                                  cur_state == S_IL_WL   ) && !|macLatency);

assign #(`delay) inst[24:24] = 'd0;
assign #(`delay) inst[23:20] = macLatency_d;


// ===============================================================
// MAC Shift Control
// ===============================================================
reg [1:0] mac_shift;
reg [1:0] mac_shift_d;
always @(posedge clk, negedge rstn) begin
  if (!rstn) begin
    mac_shift   <= 2'd3;
    mac_shift_d <= 2'd3;
  end else begin
    mac_shift_d <= mac_shift;
    mac_shift   <= 2'd3;
    case(cur_state)
      S_IM_WM : mac_shift <= 2'd2;
      S_IM_WL : mac_shift <= 2'd1;
      S_IL_WM : mac_shift <= 2'd1;
      S_IL_WL : mac_shift <= 2'd0;
      default : mac_shift <= 2'd3;
    endcase
  end
end
    
assign #(`delay) inst[31:30] = mac_shift;

endmodule
