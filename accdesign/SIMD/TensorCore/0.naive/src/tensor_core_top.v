`timescale 1ns / 1ps

// 4x4 matrix multiplication 
// C_out = A_in * B_in + C_in
module tensor_core_top #(
    parameter DWIDTH = 16          // FP16
)(
    input                               clk,
    input                               rst_n,

    input       [0:3][0:3][DWIDTH-1:0]  A_in, // 4x4 matrix
    input       [0:3][0:3][DWIDTH-1:0]  B_in, // 4x4 matrix
    input                               in_valid,

    input       [0:3][0:3][DWIDTH-1:0]  C_in, // 4x4 matrix
    input                               C_in_valid,

    output reg  [0:3][0:3][DWIDTH-1:0]  C_out, // 4x4 matrix
    output reg                          out_valid
);

    tensor_core_gemm #(
        .DWIDTH(DWIDTH)
    ) u_tensor_core_gemm (
        .A_in     (A_in ),
        .B_in     (B_in ),
        .C_in     (C_in ),
        .C_out    (C_out)
    );

    typedef enum logic [1:0] {
        IDLE  = 2'b00,
        LOAD  = 2'b01,
        CALC  = 2'b10,
        DONE  = 2'b11
    } state_t;

    state_t current_state, next_state;

    always @(posedge clk or posedge rst_n) begin
        if(rst_n) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always @(*) begin
        next_state = current_state;
        case (current_state)
            IDLE: begin
                if(in_valid) 
                    next_state = LOAD;
            end
            LOAD: begin
                // 한 사이클 후 바로 계산 상태로 넘어감
                next_state = CALC;
            end
            CALC: begin
                // 계산이 한 사이클만에 끝난다고 가정 (실제로는 여러 사이클 필요)
                next_state = DONE;
            end
            DONE: begin
                // 결과를 출력하고 IDLE로 복귀
                next_state = IDLE;
            end
        endcase
    end


endmodule

