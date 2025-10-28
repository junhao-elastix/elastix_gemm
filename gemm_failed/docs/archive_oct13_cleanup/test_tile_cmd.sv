module test_tile_cmd;
    import gemm_pkg::*;
    
    initial begin
        logic [31:0] cmd [0:3];
        logic [7:0] b = 4;
        logic [7:0] c = 4;
        logic [7:0] v = 32;
        logic [10:0] left_addr = 0;
        logic [10:0] right_addr = 528;
        logic [10:0] vec_len = v;
        
        cmd[0] = {16'd16, 8'd4, e_cmd_op_tile};
        cmd[1] = {left_addr, right_addr};
        cmd[2] = {vec_len, 11'b0};
        cmd[3] = {3'b0, v, 3'b0, c, 3'b0, b, 2'b0};
        
        $display("=== TILE Command for B=4, C=4, V=32 ===");
        $display("cmd[0] = 0x%08x (header: len=16, id=4, op=0xF2)", cmd[0]);
        $display("cmd[1] = 0x%08x (left_addr=0x%03x, right_addr=0x%03x)", cmd[1], left_addr, right_addr);
        $display("cmd[2] = 0x%08x (vec_len=%0d)", cmd[2], vec_len);
        $display("cmd[3] = 0x%08x (V=%0d, C=%0d, B=%0d)", cmd[3], v, c, b);
        $display("");
        $display("Breaking down cmd[3]:");
        $display("  bits[31:29] = 3'b0   = %3b", cmd[3][31:29]);
        $display("  bits[28:21] = V      = %8b = %3d", cmd[3][28:21], cmd[3][28:21]);
        $display("  bits[20:18] = 3'b0   = %3b", cmd[3][20:18]);
        $display("  bits[17:10] = C      = %8b = %3d", cmd[3][17:10], cmd[3][17:10]);
        $display("  bits[9:7]   = 3'b0   = %3b", cmd[3][9:7]);
        $display("  bits[6:0]   = B<<2   = %7b = %3d (B=%d)", cmd[3][6:0], cmd[3][6:0], cmd[3][6:2]);
        
        $finish;
    end
endmodule
