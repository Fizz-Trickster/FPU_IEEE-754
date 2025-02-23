module NV_NVDLA_CMAC_CORE_MAC_booth (
   code
  ,is_8bit
  ,sign
  ,src_data
  ,out_data
  ,out_inv
  );

input   [2:0] code;
input         is_8bit;
input         sign;
input  [15:0] src_data;
output [16:0] out_data;
output        out_inv;
reg     [2:0] in_code;
reg    [16:0] out_data;
reg           out_inv;


always @(
  sign
  or code
  ) begin
    in_code = {3{sign}} ^ code;
end

always @(
  is_8bit
  or in_code
  or src_data
  ) begin
    case({is_8bit, in_code})
        ///////// for 16bit /////////
        // +/- 0*src_data
        4'b0000,
        4'b0111:
        begin
            out_data = 17'h10000;
            out_inv = 1'b0;
        end

        // + 1*src_data
        4'b0001,
        4'b0010:
        begin
            out_data = {~src_data[15], src_data};
            out_inv = 1'b0;
        end

        // - 1*src_data
        4'b0101,
        4'b0110:
        begin
            out_data = {src_data[15], ~src_data};
            out_inv = 1'b1;
        end

        // + 2*src_data
        4'b0011:
        begin
            out_data = {~src_data[15], src_data[14:0], 1'b0};
            out_inv = 1'b0;
        end

        // - 2*src_data
        4'b0100:
        begin
            out_data = {src_data[15], ~src_data[14:0], 1'b1};
            out_inv = 1'b1;
        end

        ///////// for 8bit /////////
        // +/- 0*src_data
        4'b1000,
        4'b1111:
        begin
            out_data = 17'h100;
            out_inv = 1'b0;
        end

        // + 1*src_data
        4'b1001,
        4'b1010:
        begin
            out_data = {8'b0, ~src_data[7], src_data[7:0]};
            out_inv = 1'b0;
        end

        // - 1*src_data
        4'b1101,
        4'b1110:
        begin
            out_data = {8'b0, src_data[7], ~src_data[7:0]};
            out_inv = 1'b1;
        end

        // + 2*src_data
        4'b1011:
        begin
            out_data = {8'b0, ~src_data[7], src_data[6:0], 1'b0};
            out_inv = 1'b0;
        end

        // - 2*src_data
        4'b1100:
        begin
            out_data = {8'b0, src_data[7], ~src_data[6:0], 1'b1};
            out_inv = 1'b1;
        end
        default:
        begin
            out_data = 17'h10000;
            out_inv = 1'b0;
        end
    endcase
end

endmodule // NV_NVDLA_CMAC_CORE_MAC_booth

