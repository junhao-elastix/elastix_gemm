module gfp_up_align 
#(
    
    parameter int unsigned DATA_WIDTH = 16,
    parameter int unsigned IN_ELEMENTS = 14,
    parameter int unsigned OUT_ELEMENTS = 16,

    // Derived parameters - do not modify
    localparam int unsigned IN_ELEM_EN_WIDTH = $clog2(IN_ELEMENTS+1),
    localparam int unsigned OUT_ELEM_EN_WIDTH = $clog2(OUT_ELEMENTS+1)
)
(

    input clk,
    input rst,

    input  logic                                    i_data_val,
    input  logic [IN_ELEMENTS-1:0][DATA_WIDTH-1:0]  i_data,
    input  logic [IN_ELEM_EN_WIDTH-1:0]             i_data_pad, 
    input  logic                                    i_data_last,
    output logic                                    o_data_ack,

    output logic                                    o_data_val,
    output logic [OUT_ELEMENTS-1:0][DATA_WIDTH-1:0] o_data,
    output logic                                    o_data_last,
    output logic [OUT_ELEM_EN_WIDTH-1:0]            o_data_pad,
    output logic                                    i_dst_afull
);


    logic [2*OUT_ELEMENTS-1:0][DATA_WIDTH-1:0] aligmnet_double_buffer;
    logic [$clog2(2*OUT_ELEMENTS+1)-1:0]       buff_wr_ptr, buff_rd_ptr;
    logic                                      last_flag;
    
    assign o_data_ack = last_flag & i_data_val & ~i_dst_afull;

    always_ff @(posedge clk) begin
        if (rst) begin
            buff_wr_ptr <= '0;
            buff_rd_ptr <= '0;
            last_flag <= 1'b0;
            o_data_val <= 1'b0;
            o_data_last <= 1'b0;

        end

        else begin
            // Defaults:
            // -----------
            o_data_val <= 1'b0;
            o_data_last <= 1'b0;

            // Writing incoming data
            // ========================
            if (i_data_val & ~last_flag & ~i_dst_afull) begin
                for (int unsigned i = 0; i < IN_ELEMENTS; i++) begin
                    if (i < i_data_pad) begin
                        aligmnet_double_buffer[buff_wr_ptr + i] <= i_data[i];
                    end
                    
                    buff_wr_ptr <= buff_wr_ptr + IN_ELEMENTS - i_data_pad;
                end

                if (i_data_last) begin
                    last_flag <= 1'b1;
                end
            end
        
            // Reading outgoing data from bottom half
            // ==========================================
            if (buff_rd_ptr == 0 && buff_wr_ptr >= OUT_ELEMENTS) begin
                o_data_val <= 1'b1;
                o_data <= aligmnet_double_buffer[0 +: OUT_ELEMENTS];
                o_data_pad <= '0;
                buff_rd_ptr <= OUT_ELEMENTS;

                // Handling "online" last
                if (last_flag && buff_rd_ptr == OUT_ELEMENTS) begin
                    o_data_last <= 1'b1;
                    last_flag <= 1'b0;
                end

            end 

            // Reading outgoing data from top half
            // ========================================
            else if (buff_rd_ptr == OUT_ELEMENTS && buff_wr_ptr < OUT_ELEMENTS) begin
                o_data_val <= 1'b1;
                o_data <= aligmnet_double_buffer[OUT_ELEMENTS +: OUT_ELEMENTS];
                o_data_pad <= i_data_pad;
                buff_rd_ptr <= 0;

                // Handling "online" last
                if (last_flag && buff_rd_ptr == 0) begin
                    o_data_last <= 1'b1;
                    last_flag <= 1'b0;
                end
            end

            // Handling remaining data        
            // ==========================        
            else if (last_flag == 1'b1 ) begin
                o_data_val <= 1'b1;
                o_data_last <= 1'b1;
                last_flag <= 1'b0;

                if (buff_rd_ptr == 0) begin
                    o_data <= aligmnet_double_buffer[0 +: OUT_ELEMENTS];
                    o_data_pad <= OUT_ELEMENTS - buff_wr_ptr;
                end
                else begin
                    // buff_rd_ptr == OUT_ELEMENTS
                    o_data <= aligmnet_double_buffer[OUT_ELEMENTS +: OUT_ELEMENTS];
                    o_data_pad <= 2*OUT_ELEMENTS - buff_wr_ptr;
                end
            end
        end
    end 


endmodule 
