module gfp_norm #(
    parameter string TECHNOLOGY = "amd",
    
    parameter int unsigned MAN_WIDTH = 11,
    parameter int unsigned EXP_WIDTH = 5,

    parameter int unsigned IN_ELEMENTS = 16,
    parameter int unsigned GROUP_WORDS = 2, // Lines of data per group

    // Derived parameters - do not modify:
    parameter int unsigned ELEM_EN_WIDTH = $clog2(IN_ELEMENTS+1)
)
(
    input  clk,
    input  rst,

    // Input data interface
    input  logic                                                i_data_in_val,
    input  logic [IN_ELEMENTS-1:0][EXP_WIDTH + MAN_WIDTH-1:0]   i_data_in,
    input  logic [ELEM_EN_WIDTH-1:0]                            i_data_in_pad,
    input  logic                                                i_data_in_last,
    output logic                                                o_data_in_ack,

    // Output data interface
    output logic                                                o_data_out_val,
    output logic [IN_ELEMENTS-1:0][EXP_WIDTH + MAN_WIDTH-1:0]   o_data_out,
    output logic                                                o_data_out_last,
    output logic [ELEM_EN_WIDTH-1:0]                            o_data_out_pad,
    input  logic                                                i_data_out_ack
);


    // Data FIFO
    // ==========
    localparam int unsigned DATA_FIFO_DEPTH_LOG = 4;

    typedef struct packed {
        logic                                                group_last; // Last element in current group
        logic                                                last;
        logic [ELEM_EN_WIDTH-1:0]                            pad;
        logic [IN_ELEMENTS-1:0][EXP_WIDTH + MAN_WIDTH-1:0]   data;
    } data_rec_t;
    
    logic        data_fifo_wr_en;
    data_rec_t   data_fifo_wr_data;
    logic        data_fifo_wr_afull;

    logic        data_fifo_rd_en;
    data_rec_t   data_fifo_rd_data;
    logic        data_fifo_rd_empty;

    generic_fifo #(
        .TECHNOLOGY (TECHNOLOGY),                   // amd ...
        .LOG_DEPTH (DATA_FIFO_DEPTH_LOG),
        .PROG_FULL_THRESH (2**DATA_FIFO_DEPTH_LOG-8),
        .DATA_WIDTH ($bits(data_fifo_wr_data)),
        .READ_MODE ("fwft")                         // std, fwft
    )
    data_fifo
    (
        .clk(clk),
        .rst(rst),

        .wr_en(data_fifo_wr_en),
        .wr_data(data_fifo_wr_data),
        .wr_full(),
        .wr_prog_full(data_fifo_wr_afull),

        .rd_en(data_fifo_rd_en),
        .rd_data(data_fifo_rd_data),
        .rd_empty(data_fifo_rd_empty)   
    );


    // Exponent buffer
    // =================
    localparam int unsigned EXP_FIFO_DEPTH_LOG = 4;
    
    logic                   exp_fifo_wr_en;
    logic [EXP_WIDTH -1:0]  exp_fifo_wr_data;
    logic                   exp_fifo_wr_afull;

    logic                   exp_fifo_rd_en;
    logic [EXP_WIDTH-1:0]   exp_fifo_rd_data;
    logic                   exp_fifo_rd_empty;

    generic_fifo #(
        .TECHNOLOGY (TECHNOLOGY),                   // amd ...
        .LOG_DEPTH (EXP_FIFO_DEPTH_LOG),
        .PROG_FULL_THRESH (2**EXP_FIFO_DEPTH_LOG-8),
        .DATA_WIDTH (EXP_WIDTH),
        .READ_MODE ("fwft")                         // std, fwft
    )
    exp_fifo
    (
        .clk(clk),
        .rst(rst),

        .wr_en(exp_fifo_wr_en),
        .wr_data(exp_fifo_wr_data),
        .wr_full(),
        .wr_prog_full(exp_fifo_wr_afull),

        .rd_en(exp_fifo_rd_en),
        .rd_data(exp_fifo_rd_data),
        .rd_empty(exp_fifo_rd_empty)   
    );


    typedef struct packed {
        logic [EXP_WIDTH-1:0]       exp;
        logic [MAN_WIDTH-1:0]       man;
    } fp_t;
    
    // MAX exponent logic 
    // ===================
    // ToDo: To be optimized

    logic [EXP_WIDTH-1:0]   word_max_exp;

    always_comb begin
        word_max_exp = '0;

        if (i_data_in_val) begin
            for (int unsigned i = 0; i < IN_ELEMENTS; i++) begin
                fp_t curr_fp;
                curr_fp = i_data_in[i];
                
                if (i < IN_ELEMENTS - i_data_in_pad) begin
                    if (curr_fp.exp > word_max_exp) begin
                        word_max_exp = curr_fp.exp;
                    end
                end
            end 
        end
    end

    // Input data buffering process
    // --------------------------------
    logic [$clog2(GROUP_WORDS+1)-1:0]   word_id;
    logic [EXP_WIDTH-1:0]               data_max_exp;

    assign o_data_in_ack = i_data_in_val & ~data_fifo_rd_empty & ~exp_fifo_rd_empty;

    always_ff @(posedge clk) begin
        if (rst) begin
            exp_fifo_wr_en <= 1'b0;
            data_fifo_wr_en <= 1'b0;
            word_id <= '0;
            data_max_exp <= '0;

        end

        else begin
            exp_fifo_wr_en <= 1'b0;
            data_fifo_wr_en <= 1'b0;

            if (i_data_in_val & ~data_fifo_wr_afull & ~exp_fifo_wr_afull) begin
                // Write data
                data_fifo_wr_en <= 1'b1;
                data_fifo_wr_data.data <= i_data_in;
                data_fifo_wr_data.pad <= i_data_in_pad;
                data_fifo_wr_data.last <= i_data_in_last;
                
                data_fifo_wr_data.group_last <= 1'b0; // Default value
                
                if (i_data_in_last || word_id == GROUP_WORDS - 1) begin
                    word_id <= '0;
                    data_max_exp <= '0;
                    data_fifo_wr_data.group_last <= 1'b1;

                    exp_fifo_wr_en <= 1'b1;
                    exp_fifo_wr_data <= max (data_max_exp, word_max_exp);
                end

                else begin
                    data_max_exp <= max (data_max_exp, word_max_exp);
                    word_id <= word_id + 1;
                end 
            end
        end
    end

    // GFP Normalization output logic:
    // ===================================

    // Output buffer
    // ================
    localparam int unsigned OUT_FIFO_DEPTH_LOG = 5;
    
    logic        out_fifo_wr_en;
    data_rec_t   out_fifo_wr_data;
    logic        out_fifo_wr_afull;

    logic        out_fifo_rd_en;
    data_rec_t   out_fifo_rd_data;
    logic        out_fifo_rd_empty;

    assign o_data_out_val = ~out_fifo_rd_empty;
    assign o_data_out <= out_fifo_rd_data.data;
    assign o_data_out_last = out_fifo_rd_data.last;
    assign o_data_out_pad = out_fifo_rd_data.pad;
    assign out_fifo_rd_en = i_data_out_ack;

    generic_fifo #(
        .TECHNOLOGY (TECHNOLOGY),                   // amd ...
        .LOG_DEPTH (OUT_FIFO_DEPTH_LOG),
        .PROG_FULL_THRESH (2**OUT_FIFO_DEPTH_LOG-8),
        .DATA_WIDTH ($bits(out_fifo_wr_data)),
        .READ_MODE ("fwft")                         // std, fwft
    )
    out_fifo
    (
        .clk(clk),
        .rst(rst),

        .wr_en(out_fifo_wr_en),
        .wr_data(out_fifo_wr_data),
        .wr_full(),
        .wr_prog_full(out_fifo_wr_afull),

        .rd_en(out_fifo_rd_en),
        .rd_data(out_fifo_rd_data),
        .rd_empty(out_fifo_rd_empty)   
    );

    // Processing and output logic
    // ===============================
    logic                   pre_norm_valid;
    data_rec_t              pre_norm_data;
    logic [EXP_WIDTH-1:0]   pre_norm_max_exp;

    logic                   norm_valid;
    fp_t [IN_ELEMENTS-1:0]  norm_elements;
    data_rec_t              norm_data;
    fp_t [IN_ELEMENTS-1:0]  pre_norm_elements;

    assign pre_norm_elements = pre_norm_data.data;

    always_ff @(posedge clk) begin
        if (rst) begin
            out_fifo_wr_en <= 1'b0;
            norm_valid <= 1'b0;
        end

        else begin
            out_fifo_wr_en <= 1'b0;
            norm_valid <= 1'b0;
            
            // Popping pre normalized data
            // ------------------------------

            if (~out_fifo_wr_afull) begin
                if (~data_fifo_rd_empty & ~exp_fifo_rd_empty) begin
                    // Read input data
                    pre_norm_valid <= 1'b1;
                    pre_norm_data <= data_fifo_rd_data;
                    pre_norm_max_exp <= exp_fifo_rd_data;
                    data_fifo_rd_en <= 1'b1;
                    
                    if (data_fifo_rd_data.group_last) begin
                        exp_fifo_rd_en <= 1'b1;
                    end
                end 
            end

            // GFP Normalization
            if (pre_norm_valid) begin
                norm_valid <= 1'b1;
                norm_data.pad <= pre_norm_data.pad;
                norm_data.last <= pre_norm_data.last;

                for (int unsigned i=0; i<IN_ELEMENTS; i++) begin
                    fp_t curr_fp;
                    curr_fp <= pre_norm_elements[i];

                    if (i < IN_ELEMENTS - pre_norm_data.pad) begin
                        
                        norm_data[i].exp <= curr_fp.exp;

                        // No shift
                        if (curr_fp.exp == pre_norm_max_exp) begin
                            norm_elements[i].man <= curr_fp.man;
                        end

                        // Shift required
                        else begin
                            norm_elements[i].man <= curr_fp.man >> (curr_fp.exp -pre_norm_max_exp);
                        end
                    end
                end
            end

            // Writing normalized data to output FIFO
            if (norm_valid) begin
                out_fifo_wr_en <= 1'b1;
                out_fifo_wr_data.pad <= norm_data.pad;
                out_fifo_wr_data.last <= norm_data.last;
                out_fifo_wr_data.data <= norm_elements;
            end
        end
    end
endmodule
