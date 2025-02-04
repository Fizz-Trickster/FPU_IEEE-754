`timescale 1ns / 1ps

module fp16_add #(
  parameter DWIDTH = 16,
  parameter EWIDTH = 5,
  parameter MWIDTH = 10,
  parameter RWIDTH = 3,                     // Round Bit-width
  parameter BIAS   = (1 << (EWIDTH-1)) - 1  // 15 = 2^(5-1)-1
)(
    input  [DWIDTH-1:0]  a_operand, 
    input  [DWIDTH-1:0]  b_operand, 
    output [DWIDTH-1:0]  result, 
    output               Exception
);
    reg [DWIDTH-1:0] result;          

    wire signA              = a_operand[DWIDTH-1];
    wire signB              = b_operand[DWIDTH-1];

    wire [EWIDTH-1:0] expA  = a_operand[MWIDTH+:EWIDTH];
    wire [EWIDTH-1:0] expB  = b_operand[MWIDTH+:EWIDTH];

    wire [MWIDTH-1:0] fracA = a_operand[0+:MWIDTH];
    wire [MWIDTH-1:0] fracB = b_operand[0+:MWIDTH];

    // 정규화 시 hidden bit(1.fraction) 고려 -> 정규화된 수라면 hidden bit = 1
    // denormal(서브노말) 처리를 위한 간단 로직
    wire isDenormA = (~(|expA));
    wire isDenormB = (~(|expB));

    // hidden bit 세팅
    wire [MWIDTH+0+RWIDTH:0] mantA = (isDenormA) ? {1'b0, fracA, {RWIDTH{1'b0}}} : {1'b1, fracA, {RWIDTH{1'b0}}};
    wire [MWIDTH+0+RWIDTH:0] mantB = (isDenormB) ? {1'b0, fracB, {RWIDTH{1'b0}}} : {1'b1, fracB, {RWIDTH{1'b0}}};

    // 지수가 모두 0이고 가수도 0이면 => 실제 0
    wire isZeroA = (~(|expA)) && (~(|fracA));
    wire isZeroB = (~(|expB)) && (~(|fracB));

    // Infinity / NaN 검사
    // exp=11111(=31) 이고 fraction != 0 이면 NaN, fraction=0 이면 Infinity
    wire isInfA  = (&expA) && (~(|fracA));
    wire isInfB  = (&expB) && (~(|fracB));
    wire isNaNA  = (&expA) && (|fracA);
    wire isNaNB  = (&expB) && (|fracB);

    // 우선 특수 케이스 처리(우선순위)
    // NaN이 하나라도 있으면 결과는 NaN
    // Inf + Inf (동일 부호) => Inf, (서로 부호 다르면 NaN(규격적으로는 Inf - Inf = NaN))
    // Inf + 유한 => Inf
    // 0 + x => x
    reg [DWIDTH-1:0] specialCaseResult;
    reg              isSpecialCase;

    always @(*) begin
        isSpecialCase = 1'b0;
        specialCaseResult = {DWIDTH{1'b0}};

        // NaN 우선
        if (isNaNA || isNaNB) begin
            // NaN 표현(quiet NaN으로 가정, sign=0, exp=11111, frac=1111111111 정도로 세팅)
            isSpecialCase = 1'b1;
            specialCaseResult = {1'b0, {EWIDTH{1'b1}}, {MWIDTH{1'b1}}};
        end

        // Inf 관련
        else if (isInfA && isInfB) begin
            isSpecialCase = 1'b1;
            // 부호 같으면 Inf, 부호 다르면 NaN(Inf - Inf)
            if (signA == signB) begin
                specialCaseResult = {signA, {EWIDTH{1'b1}}, {MWIDTH{1'b0}}}; 
            end else begin
                specialCaseResult = {1'b0, {EWIDTH{1'b1}}, {MWIDTH{1'b1}}};
            end
        end

        else if (isInfA && ~isInfB) begin
            isSpecialCase = 1'b1;
            specialCaseResult = {signA, {EWIDTH{1'b1}}, {MWIDTH{1'b0}}};
        end
        else if (~isInfA && isInfB) begin
            isSpecialCase = 1'b1;
            specialCaseResult = {signB, {EWIDTH{1'b1}}, {MWIDTH{1'b0}}};
        end
        // 둘 다 0이거나 하나만 0일 경우
        else if (isZeroA && isZeroB) begin
            isSpecialCase = 1'b1;
            specialCaseResult = {1'b0, {EWIDTH{1'b0}}, {MWIDTH{1'b0}}};
        end
        else if (isZeroA && ~isZeroB) begin
            isSpecialCase = 1'b1;
            specialCaseResult = b_operand;
        end
        else if (~isZeroA && isZeroB) begin
            isSpecialCase = 1'b1;
            specialCaseResult = a_operand;
        end
    end

    // 특수 케이스가 아닐 경우 일반적인 부동소수점 덧셈 과정 수행
    reg [EWIDTH-1:0]        expDiff;
    reg [EWIDTH-1:0]        expMax;
    reg                     signMax;
    reg [MWIDTH+0+RWIDTH:0] alignA, alignB;

    always @(*) begin
        if (expA > expB) begin
            expDiff = expA - expB;
            expMax  = expA;
            signMax = signA;
            alignA  = mantA;
            alignB  = mantB >> expDiff; 
        end else begin
            expDiff = expB - expA;
            expMax  = expB;
            signMax = signB;
            alignA  = mantA >> expDiff;
            alignB  = mantB;
        end
    end

    // 실제 덧셈 or 뺄셈 처리
    reg [MWIDTH+1+RWIDTH:0] sum_mant; // 한 비트 carry 여유
    reg                     signResult;
    always @(*) begin
        // 부호가 같으면 더하기, 다르면 빼기
        if (signA == signB) begin
            sum_mant = alignA + alignB;
            signResult = signMax;
        end else begin
            if (alignA > alignB) begin
                sum_mant = alignA - alignB;
                signResult = (expA > expB) ? signA : 
                             (expA < expB) ? signB : signA; // 같으면 A에 맞춤
            end else if (alignA < alignB) begin
                sum_mant = alignB - alignA;
                signResult = (expA > expB) ? signA : 
                             (expA < expB) ? signB : signB; // 같으면 B에 맞춤
            end else begin
                sum_mant = {MWIDTH+1{1'b0}};
                signResult = signMax;
            end
        end
    end

    // 정규화(normalize) 로직
    // sum_mant[11] (carry out) 체크, 또는 sum_mant가 0이 아닌지 확인하여 exponent 조정
    reg [EWIDTH-1:0]        expFinal;
    reg [MWIDTH+1+RWIDTH:0] mantFinal;
    always @(*) begin
        expFinal  = expMax;
        mantFinal = {MWIDTH+1+RWIDTH{1'b0}};

        // 만약 덧셈에서 carry가 발생한 경우(예: 1.111 + 1.000 => 10.xxx)
        if (sum_mant[MWIDTH+1+RWIDTH] == 1'b1) begin
            // 한 비트 오른쪽 shift + exponent 1 증가
            mantFinal = sum_mant;
            expFinal  = expMax + 1;
        end else begin
            // carry가 없으면 그대로
            // leading zero normalize(뺄셈 시 필요)
            if (sum_mant != 0) begin
                mantFinal = sum_mant << 1;
                expFinal  = expMax;
            end else begin
                // 가수가 0이면 exponent도 0 -> +0 or -0
                mantFinal = sum_mant;
                expFinal = {EWIDTH{1'b0}};
            end
        end
    end

    // Rounding: round to nearest, ties to even
    wire             guardBit = mantFinal[RWIDTH];
    wire             roundBit = mantFinal[RWIDTH-1];
    wire             stickyBit = |mantFinal[RWIDTH-2:0];
    wire             roundUp = guardBit && (roundBit || stickyBit) || (guardBit && !roundBit && !stickyBit); 

    reg [MWIDTH-1:0] mantRounded;
    reg [EWIDTH-1:0] expRounded;
    always @(*) begin
        mantRounded = mantFinal[RWIDTH+1+:MWIDTH];
        expRounded  = expFinal;

        // overflow => Inf )
        if (expFinal >= {EWIDTH{1'b1}}) begin
            // Infinity로 처리
            mantRounded = {MWIDTH{1'b0}};
            expRounded  = {EWIDTH{1'b1}};
        end else begin
            // 반올림
            mantRounded = mantFinal[RWIDTH+1+:MWIDTH] + roundUp;
            expRounded  = expFinal;
        end
    end

    always @(*) begin
        if (isSpecialCase) begin
            result = specialCaseResult;
        end else begin
            result = {signResult, expRounded, mantRounded[MWIDTH-1:0]};
        end
    end

endmodule
