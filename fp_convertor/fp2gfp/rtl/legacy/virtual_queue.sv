package virtual_queue_pkg;
    
    localparam int unsigned READ_LENGTH_WIDTH = 10; 
    localparam int unsigned MAX_QUEUE_CNT = 64;
    localparam int unsigned QUEUE_ID_WIDTH = $clog2(MAX_QUEUE_CNT+1);
    
    
    typedef struct packed  {
        logic [READ_LENGTH_WIDTH-1:0]  length;
        logic [QUEUE_ID_WIDTH-1:0]     queue_id;
    } queue_read_cmd_t;

endpackage


module virtual_queue
    import virtual_queue_pkg::*;
#( 

    parameter int unsigned DATA_WIDTH = 16*14,     
    parameter int unsigned MEM_DEPTH = 1024 * 16,      // Total memory depth
    parameter int unsigned BLOCK_SIZE = 32,            // Block size in memory entires
    parameter int unsigned MAX_QUEUE_CNT = 64,         // Number of supported queues
    
    parameter type read_cmd_t = virtual_queue_pkg::queue_read_cmd_t,

    parameter string TECHNOLOGY = "amd",
    parameter int unsigned INGRESS_FIFO_LOG_DEPTH = 10,
    parameter int unsigned EGRESS_FIFO_LOG_DEPTH = 10,
    
    // Derived parameters - do not modify
    localparam int unsigned ADDR_WIDTH = $clog2(MEM_DEPTH+1),
    localparam int unsigned NUM_BLOCKS = $ceil(real'(MEM_DEPTH) / BLOCK_SIZE),
    localparam int unsigned BLOCK_ID_WIDTH = $clog2(NUM_BLOCKS+1),
    localparam int unsigned QUEUE_ID_WIDTH = $clog2(MAX_QUEUE_CNT+1)
)
(

    input clk,
    input rst,

    // Write interface
    input  logic                        i_wr_en, 
    input  logic [QUEUE_ID_WIDTH-1:0]   i_wr_queue_id,
    input  logic [DATA_WIDTH-1:0]       i_wr_data,
    output logic                        o_wr_af,        

    // Read command interface
    input  logic                        i_cmd_val,
    input  read_cmd_t                   i_cmd,
    output logic                        o_cmd_ack,

    // Read interface
    input  logic                        i_rd_ack,
    output logic [DATA_WIDTH-1:0]       o_rd_data,
    output logic                        o_rd_empty
);
    // Main memory
    // ---------------a
    logic [DATA_WIDTH-1:0] mem [MEM_DEPTH-1:0];
     
    // Ingress Queue 
    // -----------------
    typedef struct packed {
        logic [QUEUE_ID_WIDTH-1:0]   queue_id;
        logic [DATA_WIDTH-1:0]       data;
    } ingress_buf_data_t;

    ingress_buf_data_t ingress_q_wr_data, ingress_q_rd_data;
    
    logic ingress_q_rd_en, ingress_q_rd_empty;

    assign ingress_q_wr_data.queue_id = i_wr_queue_id;
    assign ingress_q_wr_data.data     = i_wr_data;

    generic_fifo #(
        .TECHNOLOGY (TECHNOLOGY),                   // amd ...
        .LOG_DEPTH (INGRESS_FIFO_LOG_DEPTH),
        .PROG_FULL_THRESH (2**INGRESS_FIFO_LOG_DEPTH-8),
        .DATA_WIDTH ($bits(ingress_buf_data_t)),
        .READ_MODE ("fwft")                         // std, fwft
    )
    ingress_queue_i
    (
        .clk(clk),
        .rst(rst),

        .wr_en(i_wr_en),
        .wr_data(ingress_q_wr_data),
        .wr_full(),
        .wr_prog_full(o_wr_af),

        .rd_en(ingress_q_rd_en),
        .rd_data(ingress_q_rd_data),
        .rd_empty(ingress_q_rd_empty)   
    );



    // Egress Queue 
    // -----------------

    logic [DATA_WIDTH-1:0]  egress_q_wr_data;
    logic                   egress_q_wr_en;
    logic                   egress_q_afull;

    generic_fifo #(
        .TECHNOLOGY (TECHNOLOGY),                   // amd ...
        .LOG_DEPTH (EGRESS_FIFO_LOG_DEPTH),
        .PROG_FULL_THRESH (2**EGRESS_FIFO_LOG_DEPTH-8),
        .DATA_WIDTH (DATA_WIDTH),
        .READ_MODE ("fwft")                         // std, fwft
    )
    egress_queue_i
    (
        .clk(clk),
        .rst(rst),

        .wr_en(egress_q_wr_en),
        .wr_data(egress_q_wr_data),
        .wr_full(),
        .wr_prog_full(egress_q_afull),

        .rd_en(i_rd_ack),
        .rd_data(o_rd_data),
        .rd_empty(o_rd_empty)   
    );


    // Dynamic queue controller:
    // ================================

    // 1. Free block queue
    // -----------------------
    logic                       free_block_q_wr_en, free_block_q_rd_en;
    logic                       free_block_q_rd_empty, free_block_q_wr_full;
    logic [BLOCK_ID_WIDTH-1:0]  free_block_q_wr_data, free_block_q_rd_data;

    generic_fifo #(
        .TECHNOLOGY (TECHNOLOGY),                   // amd ...
        .LOG_DEPTH (BLOCK_ID_WIDTH),
        .PROG_FULL_THRESH (2**BLOCK_ID_WIDTH-8),
        .DATA_WIDTH (BLOCK_ID_WIDTH),
        .READ_MODE ("fwft")                         // std, fwft
    )
    free_block_q_i
    (
        .clk(clk),
        .rst(rst),

        .wr_en(free_block_q_wr_en),
        .wr_data(free_block_q_wr_data),
        .wr_full(),
        .wr_prog_full(free_block_q_wr_full),

        .rd_en(free_block_q_rd_en),
        .rd_data(free_block_q_rd_data),
        .rd_empty(free_block_q_rd_empty)   
    );


    // Free block management
    // ----------------------------
    logic                      tail_block_release_en;
    logic [BLOCK_ID_WIDTH-1:0] tail_block_release_id;

    enum {
        FREE_Q_WR_INIT,
        FREE_Q_WR_IDLE
    } free_q_wr_state;

    logic [BLOCK_ID_WIDTH-1:0] block_id;

    always_ff @(posedge clk) begin
        if (rst) begin
            free_q_wr_state <= FREE_Q_WR_INIT;
            free_block_q_wr_en <= 1'b0;
            block_id <= MAX_QUEUE_CNT; // Reserve blocks for initial queue descriptors
        end
        
        else begin
            free_block_q_wr_en <= 1'b0; 

            case (free_q_wr_state) 
                FREE_Q_WR_INIT: begin
                    free_block_q_wr_en <= 1'b1;
                    free_block_q_wr_data <= block_id;
                    
                    block_id <= block_id + 1;
                    if (block_id == NUM_BLOCKS-1) begin
                        free_q_wr_state <= FREE_Q_WR_IDLE;
                    end
                end 
                
                FREE_Q_WR_IDLE: begin
                    if (tail_block_release_en) begin
                        free_block_q_wr_en <= 1'b1;
                        free_block_q_wr_data <= tail_block_release_id;
                    end
                end 

                default: begin
                    free_q_wr_state <= FREE_Q_WR_IDLE;
                end
            endcase
        end
    end

    // Queue write descriptor memory
    // ------------------------------
    typedef struct packed {
        logic [BLOCK_ID_WIDTH-1:0]              block_id;
        logic [ADDR_WIDTH-BLOCK_ID_WIDTH-1:0]   offest;
    } queue_block_desc_t;

    logic [$bits(queue_block_desc_t)-1:0]  queue_write_desc_mem [MAX_QUEUE_CNT-1:0];
    logic [$bits(queue_block_desc_t)-1:0]  queue_read_desc_mem [MAX_QUEUE_CNT-1:0];


    // Block next pointer memory:
    // ---------------------------
    typedef struct packed {
        logic [BLOCK_ID_WIDTH-1:0] next_block_id;
    } block_next_ptr_t;

    logic [$bits(block_next_ptr_t)-1:0] block_next_ptr_mem [NUM_BLOCKS-1:0];

    // Queue write descriptor managment
    // ----------------------------------
    enum {
        Q_WR_DESC_INIT,
        Q_WR_DESC_IDLE
    } q_wr_desc_state;

    logic [QUEUE_ID_WIDTH-1:0]   wr_queue_id;

    queue_block_desc_t      wr_addr;
    logic [DATA_WIDTH-1:0]  wr_data; 
    logic                   wr_en;

    always_ff @(posedge clk) begin
        if (rst) begin
            q_wr_desc_state <= Q_WR_DESC_INIT;
            wr_queue_id <= '0;
            ingress_q_rd_en <= 1'b0;
            wr_en <= 1'b0;
        end
        else begin
            // Defaults
            ingress_q_rd_en <= 1'b0; 
            wr_en <= 1'b0;

            case (q_wr_desc_state) 
                Q_WR_DESC_INIT: begin
                    if (wr_queue_id == MAX_QUEUE_CNT-1) begin
                        q_wr_desc_state <= Q_WR_DESC_IDLE;
                    end
                    
                    wr_queue_id <= wr_queue_id + 1;

                    queue_write_desc_mem[wr_queue_id].block_id <= wr_queue_id;
                    queue_write_desc_mem[wr_queue_id].offest   <= '0;

                end

                Q_WR_DESC_IDLE: begin
                    // Write process (currently full when no free blocks are available)
                    if (~ingress_q_rd_empty & ~free_block_q_rd_empty) begin
                        ingress_q_rd_en <= 1'b1;

                        wr_addr <= queue_write_desc_mem[ingress_q_rd_data.queue_id];
                        wr_data <= ingress_q_rd_data.data;
                        wr_en <= 1'b1;

                        // End of block:
                        // ----------------
                        if (queue_block_desc_t'(wr_addr.offest + 1) == BLOCK_SIZE) begin
                            // Assign new block for next write operation
                            free_block_q_rd_en <= 1'b1;
                            queue_write_desc_mem[ingress_q_rd_data.queue_id].block_id <= free_block_q_rd_data;
                            queue_write_desc_mem[ingress_q_rd_data.queue_id].offest <= '0;

                            block_next_ptr_mem[wr_addr.block_id].next_block_id <= free_block_q_rd_data;
                        end

                        // Not end of block:
                        // ------------------
                        else begin
                            queue_write_desc_mem[ingress_q_rd_data.queue_id].offest <= queue_write_desc_mem[ingress_q_rd_data.queue_id].offest + 1;
                        end 
                    end
                end

                default: begin
                    q_wr_desc_state <= Q_WR_DESC_IDLE;
                end
            endcase
        end
    end

    // Queue read descriptor managment:
    // ----------------------------------
    enum {
        Q_RD_DESC_INIT,
        Q_RD_DESC_IDLE,
        Q_RD_DESC_CMD,
        Q_RD_DESC_CLOSE
    } q_rd_desc_state;

    logic [QUEUE_ID_WIDTH-1:0]   rd_queue_id;

    read_cmd_t            rd_cmd; 
    queue_block_desc_t    tail_block_desc;
    queue_block_desc_t    head_block_desc;

    always_ff @(posedge clk) begin

        if (rst) begin
            rd_queue_id <= '0;
            q_rd_desc_state <= Q_RD_DESC_INIT;
            egress_q_wr_en <= 1'b0; 
            o_cmd_ack <= 1'b0; 

            tail_block_release_en <= 1'b0;
        end

        else begin
            // Defaults
            egress_q_wr_en <= 1'b0; 
            o_cmd_ack <= 1'b0; 
            tail_block_release_en <= 1'b0;

            // Alwasy update the read descriptor memory
            queue_read_desc_mem[rd_cmd.queue_id] <= tail_block_desc;
            
            case (q_rd_desc_state) 
                Q_RD_DESC_INIT: begin
                    if (rd_queue_id == MAX_QUEUE_CNT-1) begin
                        q_rd_desc_state <= Q_RD_DESC_IDLE;
                    end
                    
                    rd_queue_id <= rd_queue_id + 1;

                    queue_read_desc_mem[rd_queue_id].block_id <= rd_queue_id;
                    queue_read_desc_mem[rd_queue_id].offest   <= '0;

                end

                Q_RD_DESC_IDLE: begin
                    if (i_cmd_val) begin
                        rd_cmd    <= i_cmd;
                        o_cmd_ack <= 1'b1;
                        
                        q_rd_desc_state <= Q_RD_DESC_CMD;
                        tail_block_desc   <= queue_read_desc_mem[rd_cmd.queue_id];
                        head_block_desc   <= queue_read_desc_mem[rd_cmd.queue_id];
                    end

                end

                Q_RD_DESC_CMD: begin

                    // When data is available 
                    if (head_block_desc !== tail_block_desc) begin
                    
                        egress_q_wr_en <= 1'b1;
                        egress_q_wr_data <= mem[tail_block_desc];
                        
                        rd_cmd.length <= rd_cmd.length - 1;
                        
                        
                        // Next block requried:
                        if (tail_block_desc.offset == BLOCK_SIZE-1) begin
                            tail_block_desc.offset <= '0;
                            tail_block_desc.block_id <= block_next_ptr_mem[tail_block_desc.block_id].next_block_id;

                            // Release current block
                            tail_block_release_en <= 1'b1;
                            tail_block_release_id <= tail_block_desc.block_id;

                        end

                        // Still more to read from block:
                        else begin
                            tail_block_desc.offset <= tail_block_desc.offset + 1;
                        end

                        rd_cmd.length <= rd_cmd.length - 1;

                        // Last read in command
                        if (rd_cmd.length == 1) begin
                            q_rd_desc_state <= Q_RD_DESC_IDLE;
                        end
                    end 
                end

                default: begin
                    q_rd_desc_state <= Q_RD_DESC_IDLE;
                end
            endcase
        end
    end

    


    
    
    








endmodule