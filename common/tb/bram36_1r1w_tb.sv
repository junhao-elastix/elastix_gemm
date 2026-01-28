module bram36_1r1w_tb #() ();

    localparam tests_p = 512;

    localparam addr_width_p = 9;
    localparam data_width_p = 1024;
    localparam reg_out_p = 1;

    logic r_clk, r_reset;
    logic w_clk, w_reset;

    logic r_v_i;
    logic [addr_width_p-1:0] r_addr_i;
    logic r_v_o;
    logic [data_width_p-1:0] r_data_o;

    logic w_v_i;
    logic [addr_width_p-1:0] w_addr_i;
    logic [data_width_p-1:0] w_data_i;
    logic [data_width_p/8-1:0] w_en_i;

    logic [data_width_p-1:0] mem [0:2**addr_width_p-1];

    bram36_1r1w #(
        .addr_width_p(addr_width_p),
        .data_width_p(data_width_p),
        .reg_out_p(reg_out_p)
    ) dut (
        .r_clk_i(r_clk),
        .r_reset_i(r_reset),
        .r_v_i(r_v_i),
        .r_addr_i(r_addr_i),
        .r_v_o(r_v_o),
        .r_data_o(r_data_o),

        .w_clk_i(w_clk),
        .w_reset_i(w_reset),
        .w_v_i(w_v_i),
        .w_addr_i(w_addr_i),
        .w_data_i(w_data_i),
        .w_en_i(w_en_i)
    );

    initial begin
        r_clk = 0;
        forever #5 r_clk = ~r_clk;
    end

    initial begin
        w_clk = 0;
        forever #10 w_clk = ~w_clk;
    end

    initial begin
        r_reset = 1;
        w_reset = 1;
        r_v_i = 0;
        w_v_i = 0;
        w_en_i = '0;
        repeat (5) @(negedge r_clk);
        repeat (5) @(negedge w_clk);
        r_reset = 0;
        w_reset = 0;
        repeat (5) @(negedge r_clk);
        repeat (5) @(negedge w_clk);

        // Write some data
        for (int i = 0; i < tests_p; i++) begin
            @(negedge w_clk);
            w_v_i = 1;
            w_addr_i = i;
            for (int j = 0; j < data_width_p/32; j++) begin
                w_data_i[j * 32 +: 32] = $urandom;
            end
            w_en_i = '1;
            mem[w_addr_i] = w_data_i;
            //$display("Wrote %0h to address %0d", w_data_i, w_addr_i);
        end
        @(negedge w_clk);
        w_v_i = 0;
        w_en_i = '0;

        // Read the data back
        for (int i = 0; i < tests_p; i++) begin
            @(negedge r_clk);
            r_v_i = 1;
            r_addr_i = i;
        end
        @(negedge r_clk);
        r_v_i = 0;
        repeat (10) @(negedge r_clk);
    end

    initial begin
        for (int i = 0; i < tests_p; i++) begin
            wait(r_v_o);
            @(negedge r_clk);
            //$display("Read %0h from address %0d", r_data_o, i);
            assert(r_data_o == mem[i]) else begin
                $error("Data mismatch at address %0d: expected %0h, got %0h", i, mem[i], r_data_o);
                $finish;
            end
        end
        $display("All data matched!");
        $finish;
    end

endmodule