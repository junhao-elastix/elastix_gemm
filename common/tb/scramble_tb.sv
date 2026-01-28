module scramble_tb;

    parameter els_p = 16;
    parameter width_p = 32;
    parameter size_width_p = 2;

    logic [els_p-1:0][width_p-1:0] data_i;
    logic [size_width_p-1:0] size_i;

    logic [els_p-1:0][width_p-1:0] data_o;

    scramble #(
        .els_p(els_p),
        .width_p(width_p),
        .size_width_p(size_width_p)
    ) dut (
        .data_i(data_i),
        .size_i(size_i),
        .data_o(data_o)
    );

    initial begin
        for (int i = 0; i < els_p; i++) begin
            data_i[i] = $urandom;
        end

        $display("Input Data:");
        for (int i = 0; i < els_p; i++) begin
            $write("%x ", data_i[i]);
        end
        $write("\n\n");

        for (int s = 0; s < (1 << size_width_p); s++) begin
            size_i = s;
            #10;
            $display("Size: %0d", s);
            for (int i = 0; i < els_p; i++) begin
                $write("%x ", data_o[i]);
            end
            $write("\n");
        end

        $finish;
    end
endmodule