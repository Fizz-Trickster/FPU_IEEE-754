`timescale 1ns / 1ps

// 4x4 matrix multiplication with Kulisch Accumulation
// C_out = A_in * B_in + C_in
module tensor_core_top #(
    parameter NUM    = 4,        // Number of elements: 4
    parameter DWIDTH = 16,       // FP16 bit-width : 16-bit
    parameter EWIDTH = 5,        // FP16 bit-width exponent: 5-bit
    parameter MWIDTH = 10,       // FP16 bit-width mantissa: 10-bit
    parameter AWIDTH = 92        // Accumulation bit-width: 92-bit (1(sign) + 11(k) + 32(integer) + 48(fraction))
)(
    input                                       clk,
    input                                       rst_n,

    input       [NUM-1:0][NUM-1:0][DWIDTH-1:0]  A_in,           // 4x4 matrix
    input       [NUM-1:0][NUM-1:0][DWIDTH-1:0]  B_in,           // 4x4 matrix

    input       [NUM-1:0][NUM-1:0][AWIDTH-1:0]  C_sum_in,       // 4x4 matrix
    input       [NUM-1:0][NUM-1:0][AWIDTH-1:0]  C_carry_in,     // 4x4 matrix
    input                                       C_valid_in,

    output      [NUM-1:0][NUM-1:0][AWIDTH-1:0]  C_sum_out,      // 4x4 matrix
    output      [NUM-1:0][NUM-1:0][AWIDTH-1:0]  C_carry_out    // 4x4 matrix
);

    // MMA 모듈 연결  
    tensor_core_gemm #(
        .NUM             ( NUM         ),
        .DWIDTH          ( DWIDTH      ),
        .EWIDTH          ( EWIDTH      ),
        .MWIDTH          ( MWIDTH      ),
        .AWIDTH          ( AWIDTH      )
    ) u_tensor_core_gemm (
        .A_in            ( A_in        ),
        .B_in            ( B_in        ),

        .C_sum_in        ( C_sum_in    ),
        .C_carry_in      ( C_carry_in  ),
        .C_valid_in      ( C_valid_in  ),

        .C_sum_out       ( C_sum_out   ),
        .C_carry_out     ( C_carry_out )
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

    // 상태 머신
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

    //// 출력 및 내부 레지스터 갱신
    //always @(posedge clk or posedge rst_n) begin
    //    if(rst_n) begin
    //        A_reg     <= {DWIDTH*16{1'b0}};
    //        B_reg     <= {DWIDTH*16{1'b0}};
    //        C_out     <= {DWIDTH*16{1'b0}};
    //        out_valid <= 1'b0;
    //    end else begin
    //        case (current_state)
    //            IDLE: begin
    //                out_valid <= 1'b0;
    //                // 대기 중
    //            end
    //            LOAD: begin
    //                // 입력을 레지스터에 저장
    //                A_reg     <= A_in;
    //                B_reg     <= B_in;
    //                out_valid <= 1'b0;
    //            end
    //            CALC: begin
    //                // 여기서는 실제로 MMA 모듈이 계산을 진행 (파이프라인이나 여러 사이클이 걸릴 수 있음)
    //                // 예제에서는 한 사이클 후 C_wire에 결과가 나온다고 가정
    //            end
    //            DONE: begin
    //                // 계산 결과를 출력 레지스터에 저장
    //                C_out     <= C_wire;
    //                out_valid <= 1'b1;
    //            end
    //        endcase
    //    end
    //end

endmodule

////
//// 4x4 행렬 곱셈-누적(MMA) 모듈
//// A, B는 각각 4x4 행렬, C는 그 결과
////
//module mma_4x4 #(
//    parameter DWIDTH = 16
//)(
//    input  wire [DWIDTH*16-1:0] A, // A 행렬 (4x4)
//    input  wire [DWIDTH*16-1:0] B, // B 행렬 (4x4)
//    output wire [DWIDTH*16-1:0] C  // C = A x B (4x4)
//);
//
//    // 행렬 A, B에서 각 원소 추출
//    // A_ij: A의 (i,j) 원소, B_ij: B의 (i,j) 원소
//    // 4x4 행렬 -> index: A[i][j], i,j = 0..3
//    // 예시) A[0][0] = A[(0*4 + 0)*DWIDTH +: DWIDTH]
//
//    // A 행렬 원소
//    wire signed [DWIDTH-1:0] A_mat [0:3][0:3];
//    // B 행렬 원소
//    wire signed [DWIDTH-1:0] B_mat [0:3][0:3];
//    // 결과 행렬 C 원소
//    wire signed [DWIDTH-1:0] C_mat [0:3][0:3];
//
//    genvar i, j;
//    generate
//        for(i = 0; i < 4; i = i + 1) begin : ROW
//            for(j = 0; j < 4; j = j + 1) begin : COL
//                // 각 원소를 A_in, B_in에서 추출
//                assign A_mat[i][j] = A[((i*4 + j)*DWIDTH) +: DWIDTH];
//                assign B_mat[i][j] = B[((i*4 + j)*DWIDTH) +: DWIDTH];
//            end
//        end
//    endgenerate
//
//    // C = A x B (4x4 행렬 곱셈)
//    // C[i][j] = Σ_k (A[i][k] * B[k][j]),  k = 0..3
//    // 여기서는 각 원소를 signed 정수 곱으로 단순 처리
//
//    genvar r, c, k;
//    generate
//        for(r = 0; r < 4; r = r + 1) begin : rowC
//            for(c = 0; c < 4; c = c + 1) begin : colC
//                // 누산용 임시 레지스터
//                reg signed [2*DWIDTH-1:0] sum; // 곱셈 결과가 더 클 수 있으므로 2*DWIDTH로 잡음
//                always @(*) begin
//                    sum = 0;
//                    for(k = 0; k < 4; k = k + 1) begin
//                        sum = sum + (A_mat[r][k] * B_mat[k][c]);
//                    end
//                end
//                // 결과를 DWIDTH 크기로 자른다고 가정 (오버플로우는 단순히 자름)
//                assign C_mat[r][c] = sum[DWIDTH-1:0];
//            end
//        end
//    endgenerate
//
//    // C_mat -> C (직렬화)
//    generate
//        for(i = 0; i < 4; i = i + 1) begin : row_serial
//            for(j = 0; j < 4; j = j + 1) begin : col_serial
//                assign C[((i*4 + j)*DWIDTH) +: DWIDTH] = C_mat[i][j];
//            end
//        end
//    endgenerate
//
//endmodule
