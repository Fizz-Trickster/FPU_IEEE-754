module wallace_tree_param #(
    parameter PARTIAL_COUNT = 6, // 부분곱 개수
    parameter BW            = 22 // 각 부분곱의 비트폭
)(
    input  wire [BW-1:0] in [PARTIAL_COUNT], // 입력 부분곱들(SV 배열)
    output reg  [BW-1:0] sum,
    output reg  [BW-1:0] carry
);

    //--------------------------------------------------------------------------
    // 1) 필요한 스테이지 수 계산 함수
    //    - Wallace 트리는 "3개씩 CSA" -> "2개 출력" 이므로
    //      남은 partial product 개수가 2 이하가 될 때까지 반복
    //--------------------------------------------------------------------------
    function automatic int needed_stages(input int n);
        int cnt, stg;
        begin
            cnt = n;
            stg = 0;
            while (cnt > 2) begin
                // 3개를 1그룹으로 묶으면 -> 2개가 되어 나옴
                // 따라서 새로 생기는 개수는 (cnt/3)*2 + (cnt % 3)
                // (나머지 1개나 2개는 그냥 그대로 다음 단계로 넘어옴)
                cnt = (cnt/3)*2 + (cnt % 3);
                stg++;
            end
            return stg;
        end
    endfunction

    // 0개/1개/2개 이하이면 스테이지가 0이 된다.
    localparam int STAGES = needed_stages(PARTIAL_COUNT);


    //--------------------------------------------------------------------------
    // 2) 각 Stage마다 partial product를 모아두는 2차원 배열
    //    partials[stage][index]
    //--------------------------------------------------------------------------
    // 최대 partial product 개수는 단계마다 줄어들지만,
    // 편의상 최악의 경우(초기 PARTIAL_COUNT)만큼 할당
    //--------------------------------------------------------------------------
    logic [BW-1:0] partials [STAGES+1][PARTIAL_COUNT]; 
    int            size     [STAGES+1];  // 각 stage에서의 partial 개수

    // 초기 stage(0단계) 입력 할당
    // size[0] = PARTIAL_COUNT, partials[0][..] = in[..]
    initial begin
        size[0] = PARTIAL_COUNT;
        for (int k = 0; k < PARTIAL_COUNT; k++)
            partials[0][k] = in[k];
    end

    //--------------------------------------------------------------------------
    // 3) 각 Stage에서 3개씩 CSA로 묶어 -> 2개를 생성
    //    leftover(3으로 나누고 남은) 1~2개는 그대로 복사
    //--------------------------------------------------------------------------
    generate
        genvar stg;
        for (stg = 0; stg < STAGES; stg++) begin : STAGE_GEN
            // 다음 스테이지 크기
            // next_count = (size[stg]/3)*2 + (size[stg] % 3)
            // (아래 코드는 procedural block에서 계산)
            always_comb begin
                int curr_size = size[stg];
                int group3    = curr_size / 3; 
                int leftover  = curr_size % 3; 
                int next_cnt  = group3*2 + leftover;

                size[stg+1] = next_cnt;

                // 먼저 모든 값을 0으로 초기화(안전)
                for (int x = 0; x < PARTIAL_COUNT; x++) begin
                    partials[stg+1][x] = '0;
                end

                // CSA로 3개씩 묶어서 sum, carry 생성
                int out_idx = 0;
                for (int g = 0; g < group3; g++) begin
                    // 묶을 인덱스 = 3*g, 3*g+1, 3*g+2
                    logic [BW-1:0] s, c;
                    csa #(.BW(BW)) csa_inst (
                        .x(partials[stg][3*g]),
                        .y(partials[stg][3*g+1]),
                        .z(partials[stg][3*g+2]),
                        .s(s),
                        .c(c)
                    );
                    partials[stg+1][out_idx]   = s;
                    partials[stg+1][out_idx+1] = c;
                    out_idx += 2;
                end

                // leftover 복사
                // leftover가 1이면 그것만, 2면 2개 그대로 복사
                for (int r = 0; r < leftover; r++) begin
                    partials[stg+1][out_idx+r] = partials[stg][3*group3 + r];
                end
            end
        end
    endgenerate

    //--------------------------------------------------------------------------
    // 4) 최종 Stage 결과 (STAGES 단계 후)
    //    - size[STAGES]가 2 이상이면 partials[STAGES][0..1]를 sum/carry
    //    - 1이면 partials[STAGES][0]만 sum, carry=0
    //    - 0이면(극단적 케이스) sum=0, carry=0
    //--------------------------------------------------------------------------
    always @(*) begin
        if (size[STAGES] >= 2) begin
            sum   = partials[STAGES][0];
            carry = partials[STAGES][1];
        end
        else if (size[STAGES] == 1) begin
            sum   = partials[STAGES][0];
            carry = '0;
        end
        else begin
            sum   = '0;
            carry = '0;
        end
    end

endmodule

module csa #(
    parameter int BW = 8
)(
    input  logic [BW-1:0] x,
    input  logic [BW-1:0] y,
    input  logic [BW-1:0] z,
    output logic [BW-1:0] s,
    output logic [BW-1:0] c
);
    // Full Adder를 비트별로 병렬 수행한 효과:
    // s = x ^ y ^ z
    // c = (x & y) | (y & z) | (z & x)
    always_comb begin
        s = x ^ y ^ z;
        c = (x & y) | (y & z) | (z & x);
    end
endmodule
