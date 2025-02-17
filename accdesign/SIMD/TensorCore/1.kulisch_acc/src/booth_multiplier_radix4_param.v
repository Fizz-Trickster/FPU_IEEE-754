module booth_multiplier_radix4_param #(
    parameter DWIDTH = 11
)(
    input  signed [1*DWIDTH-1:0] A,
    input  signed [1*DWIDTH-1:0] B,
    output        [2*DWIDTH-1:0] sum,     // 최종 Wallace 트리 결과 중 sum
    output        [2*DWIDTH-1:0] carry    // 최종 Wallace 트리 결과 중 carry
);

    //-------------------------------------------------------------------------
    // 0) 내부 파라미터 / 로컬파라미터
    //-------------------------------------------------------------------------
    // B를 Booth용으로 부호 확장시 (WIDTH+2)비트
    // 실제 partial product는 2비트씩 끊으면 대략 ceil(WIDTH/2) + 1 단계 처리
    // (아래처럼 (WIDTH+1)/2 로 잡음)
    //-------------------------------------------------------------------------
    localparam EXT_LEN     = WIDTH + 2;               
    localparam GROUP_COUNT = (WIDTH+1)/2; // 부분곱 개수

    //-------------------------------------------------------------------------
    // 1) 부호 확장: B → B_ext (WIDTH+2)비트
    // 상위 비트 복제
    //-------------------------------------------------------------------------
    wire signed [EXT_LEN-1:0] B_ext;
    assign B_ext = {{2{B[DWIDTH-1]}}, B};

    //-------------------------------------------------------------------------
    // 2) Radix-4 Booth 인코딩 함수
    //    3비트를 보고 0, ±1, ±2 배를 결정
    //-------------------------------------------------------------------------
    function [2:0] booth_code(
        input [2:0] bits
    );
        // bits = {b2, b1, b0}
        //   000, 111 → 0
        //   001, 010 → +1
        //   011      → +2
        //   100      → -2
        //   101, 110 → -1
        case (bits)
            3'b000,
            3'b111: booth_code = 3'b000; //  0
            3'b001,
            3'b010: booth_code = 3'b001; // +1
            3'b011: booth_code = 3'b010; // +2
            3'b100: booth_code = 3'b100; // -2
            3'b101,
            3'b110: booth_code = 3'b011; // -1
            default: booth_code = 3'b000; // safety
        endcase
    endfunction

    //-------------------------------------------------------------------------
    // 3) 부분곱(Partial Product) 생성
    //-------------------------------------------------------------------------
    // - 총 GROUP_COUNT개의 partial product를 생성
    // - A 역시 부호 확장하여 연산
    // - booth_code(bits)에 따라 0, ±A, ±2A를 2*i만큼 왼쪽 쉬프트
    //-------------------------------------------------------------------------
    wire signed [2*DWIDTH-1:0] partial_prod [GROUP_COUNT]; // SV 배열 포트

    // A를 2*WIDTH로 sign-extend
    wire signed [2*DWIDTH-1:0] A_ext;
    assign A_ext = {{(DWIDTH){A[DWIDTH-1]}}, A};

    genvar i;
    generate
        for (i = 0; i < GROUP_COUNT; i++) begin : GEN_PARTIAL
            // B_ext에서 3비트 추출
            // 예: i=0 → B_ext[2:0], i=1 → B_ext[4:2], ...
            wire [2:0] bits;
            assign bits = B_ext[2*i +: 3];

            // 각 i 단계에서 연산 결과
            reg signed [2*DWIDTH-1:0] sel;

            always @(*) begin
                unique case (booth_code(bits))
                    3'b000: sel = 0;                //  0
                    3'b001: sel = A_ext;            // +1 * A
                    3'b010: sel = A_ext <<< 1;      // +2 * A
                    3'b011: sel = -A_ext;           // -1 * A
                    3'b100: sel = -(A_ext <<< 1);   // -2 * A
                    default: sel = 0;
                endcase
            end

            // 2*i만큼 왼쪽 쉬프트
            assign partial_prod[i] = sel <<< (2*i);
        end
    endgenerate

    //-------------------------------------------------------------------------
    // 4) Wallace 트리로 부분곱 합산
    //-------------------------------------------------------------------------
    // - GROUP_COUNT개의 2*WIDTH비트 부분곱을 입력받아,
    //   최종적으로 2개의 Row(sum, carry)만 남길 때까지
    //   병렬 CSA로 반복 압축(reduction)하는 구조
    // - wallace_tree_param 모듈에 위 partial_prod를 전달
    //-------------------------------------------------------------------------
    wire [2*DWIDTH-1:0] w_sum;
    wire [2*DWIDTH-1:0] w_carry;

    wallace_tree_param #(
        .PARTIAL_COUNT(GROUP_COUNT),
        .BW(2*DWIDTH)
    ) wtree (
        .in (partial_prod),
        .sum (w_sum),
        .carry (w_carry)
    );

    //-------------------------------------------------------------------------
    // 모듈 최종 출력
    //-------------------------------------------------------------------------
    assign sum   = w_sum;
    assign carry = w_carry;

endmodule
