module clz_tb
    import common_pkg::*;
#(
    localparam width_p = 58
) ();

    localparam tests_lp = 1000;
    localparam out_width_lp = $clog2(width_p+1);

    logic [width_p-1:0] data;
    logic [out_width_lp-1:0] clz, expected_clz;

    clz #(
        .width_p(width_p)
    ) dut (
        .data_i(data),
        .clz_o(clz)
    );

    initial begin
        for (int i = 0; i < tests_lp; i++) begin
            data = (i == 0) ? '0 : (i == 1) ? '1 : {(cdiv(width_p, 32)){$urandom()}};
            #10;
            expected_clz = width_p;
            for (int k = width_p-1; k >= 0; k--) begin
              if (data[k]) begin
                  expected_clz = width_p - 1 - k;
                  break;
              end
            end
            $display("data: %b, clz: %0d", data, clz);
            if (clz !== expected_clz) begin
                $display("ERROR: Mismatch for data %b: expected %0d, got %0d", data, expected_clz, clz);
                $finish;
            end
        end
        $display("All tests passed!");
        $finish;
    end
endmodule