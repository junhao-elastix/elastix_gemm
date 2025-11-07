// ------------------------------------------------------------------
// DMA BRAM Bridge - BRAM Responder with Internal Write Port Support
// 
// This module extends the original axi_bram_responder functionality by adding
// internal write port support for the MS2.0 GEMM engine. It maintains the same
// AXI4 interface as the original but includes additional internal ports.
//
// Key Features:
// - Full AXI4 responder interface compatible with original axi_bram_responder
// - Internal write port for GEMM engine result data
// - Dual-port BRAM storage (2x BRAM72K instances for 256-bit data)
// - Support for partial writes via byte strobe control
// - Legacy processing interface maintained for compatibility (disabled)
//
// Internal Port Usage:
// - Internal write port used by MS2.0 GEMM engine for result storage
// - PCIe can read processed results via standard AXI interface
// - Write conflicts handled between internal and external writes
//
// BRAM Organization:
// - Uses 2x BRAM72K instances to handle 256-bit data width
// - Lower 144 bits stored in xact_mem_lo
// - Upper 144 bits stored in xact_mem_hi (with 32-bit padding)
// - 9-bit address space (512 locations) for transaction storage
//
// Author: Junhao Pan
// Date:
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dma_bram_bridge
  #(
    parameter TGT_DATA_WIDTH = 0, // Target data width.
    parameter TGT_ADDR_WIDTH = 0,
    parameter NAP_COL        = 4'hx,
    parameter NAP_ROW        = 4'hx,
    parameter NAP_N2S_ARB_SCHED  = 32'hxxxxxxxx, // north-to-south arbitration schedule
    parameter NAP_S2N_ARB_SCHED  = 32'hxxxxxxxx, // south-to-north arbitration schedule
    parameter string PROBE_NAME  = "bram_ext"    // When multiple responders in a design, and Snapshot
                                                 // is enabled, then each probe needs a unique name
    )
   (
    // Inputs
    input wire i_clk,
    input wire i_reset_n,       // Negative synchronous reset
    input wire i_bram_inc42_en, // Legacy processing enable (unused, kept for compatibility)
    
    // Internal Access Ports (for MS2.0 GEMM engine result writer)
    input  wire                              i_internal_rd_en,     // FSM read enable
    input  wire [8:0]                        i_internal_rd_addr,   // FSM read address (0-127)
    output logic [255:0]                     o_internal_rd_data,   // FSM read data (int16 at [15:0])

    input  wire                              i_internal_wr_en,     // FSM write enable
    input  wire [8:0]                        i_internal_wr_addr,   // FSM write address (0-127)
    input  wire [255:0]                      i_internal_wr_data,   // FSM write data (int16 at [15:0])
    input  wire [31:0]                       i_internal_wr_strobe  // FSM write byte enables
    );



   localparam AXI4_ID_WIDTH             = 8;
   localparam AXI4_RESPONDER_ADDR_WIDTH = 9;                   // BRAM for transactions is 512 deep
   localparam NAP_DATA_WIDTH            = TGT_DATA_WIDTH;
   localparam NAP_ADDR_WIDTH            = TGT_ADDR_WIDTH;



   logic [NAP_DATA_WIDTH-1:0]               xact_r_dout;       // Read data
   logic [AXI4_ID_WIDTH-1:0]                xact_ar_id;        // AR transaction ID
   logic [AXI4_RESPONDER_ADDR_WIDTH-1:0]    xact_ar_addr;      // AR transaction address
   logic [6 -1:0]                           xact_ar_len;       // AR transaction length, NoC has limit of 16
                                                               // Allow support for up to 64
   logic [1:0]                              xact_ar_burst;     // Burst type for AR transaction
   logic                                    xact_rd_en;        // Set read enable on BRAM
   logic                                    xact_read_valid;   // Handling a valid read
   logic                                    xact_read_valid_d;
   
   logic [1:0]                              xact_rd_avail;     // 2-pipe stage to when read data available
   logic [3:0]                              xact_ar_len_d1;    // delay 1 cycle
   logic [3:0]                              xact_ar_len_d2;    // delay 2 cycles to match with read out
   
   logic [NAP_DATA_WIDTH-1:0]               xact_r_dout_d1;    // read data flop, needed to buffer on ready low
   logic [NAP_DATA_WIDTH-1:0]               xact_r_dout_d2;    // read data flop, needed to buffer on ready low
   logic [1:0]                              r_dout_valid;      // which data buffers are valid
   logic                                    hold_read;         // ready low while vaild high
   logic                                    xact_r_last_dout_q;
   logic                                    xact_r_last_dout;
   logic                                    xact_r_last_d1;
   logic                                    xact_r_last_d2;
   
   // synthesis synthesis_off
   // Following signal does not drive any loads, kept for simulation purposes only
   logic                             read_conflict;     // Trying to read at same address as current write
   // synthesis synthesis_on
   

   logic [NAP_DATA_WIDTH-1:0]               xact_w_din;        // Write data
   logic [NAP_DATA_WIDTH-1:0]               xact_w_din_processed; // Write data (pass-through)
   logic [AXI4_ID_WIDTH-1:0]                xact_aw_id;        // AW transaction ID
   logic [AXI4_RESPONDER_ADDR_WIDTH-1:0]    xact_aw_addr;      // AW transaction address
   logic [7:0]                              xact_aw_len;       // AW transaction length, limit of 16
   logic [1:0]                              xact_aw_burst;     // Burst type for AW transaction
   logic [31:0]                             xact_wstrb;        // Write byte strobe
   logic                                    xact_wr_en;        // Set write enable on BRAM
   logic                                    xact_write_valid;  // Handling a valid write
   logic                                    xact_write_valid_d;
   logic                                    xact_wlast;
   
   logic                                    write_conflict;    // Trying to write at same address as current read
   
   logic [1:0]                              xact_sbit_error_0;
   logic [1:0]                              xact_sbit_error_1;
   logic [1:0]                              xact_dbit_error_0;
   logic [1:0]                              xact_dbit_error_1;
   logic                                    nap_output_rstn;
   logic                                    nap_error_valid;
   logic [2:0]                              nap_error_info;
   
   logic                                    aw_registered;
   logic                                    aw_sequence_error;
   logic                                    w_registered;
   logic                                    b_registered;


   // Create NAP interface
   // This contains all the AXI signals for NAP
   t_AXI4 #(
            .DATA_WIDTH (NAP_DATA_WIDTH),
            .ADDR_WIDTH (NAP_ADDR_WIDTH),
            .LEN_WIDTH  (8),
            .ID_WIDTH   (8))
   axi_if_mas() /* synthesis syn_keep=1 */;


   // Instantiate the NAP
   nap_initiator_wrapper
     #(
       .COLUMN (NAP_COL),
       .ROW    (NAP_ROW),
       .N2S_ARB_SCHED (NAP_N2S_ARB_SCHED),
       .S2N_ARB_SCHED (NAP_S2N_ARB_SCHED)
       )
   i_axi_initiator_nap(
                    // Inputs
                    .i_clk          (i_clk),
                    .i_reset_n      (i_reset_n),    // Negative synchronous reset
                    .nap            (axi_if_mas),   // Module is an initiator
                    // Outputs
                    .o_output_rstn  (nap_output_rstn),
                    .o_error_valid  (nap_error_valid),
                    .o_error_info   (nap_error_info)
                    );


   //-----------------------------------
   // Simple dual-port memory to
   // respond to write and read
   // transactions
   // address for this will be 9 bits
   // so that it fits nicely in a BRAM
   //-----------------------------------
   logic [31:0]                      dummy_dout; // unused data bits

   
   // Internal FSM access signals with muxing
   // internal_bram_rd_data_lo/hi removed - not used after cleanup
   logic [8:0]   actual_rd_addr;
   logic [8:0]   actual_wr_addr;
   logic [255:0] actual_wr_data;
   logic         actual_wr_en;
   logic [31:0]  actual_wstrb;
   logic         actual_rd_en;
   
   // Mux logic: INTERNAL WRITES NOW HAVE PRIORITY (Oct 10, 2025 fix)
   // Reason: Engine result writes are time-critical and infrequent
   // DMA can be retried, but blocking engine writes causes result loss
   logic dma_active;
   logic internal_wr_active;

   assign internal_wr_active = i_internal_wr_en;  // Internal write request
   assign dma_active = (xact_write_valid | xact_read_valid) & ~internal_wr_active;  // DMA only when no internal write

   // Read path mux (reads can coexist with internal writes)
   assign actual_rd_en   = i_internal_rd_en ? i_internal_rd_en : (dma_active ? xact_rd_en : 1'b0);
   assign actual_rd_addr = i_internal_rd_en ? i_internal_rd_addr : (dma_active ? xact_ar_addr : 9'b0);

   // Write path mux - INTERNAL WRITES HAVE PRIORITY
   assign actual_wr_en   = internal_wr_active ? i_internal_wr_en : (dma_active ? xact_wr_en : 1'b0);
   assign actual_wr_addr = internal_wr_active ? i_internal_wr_addr : (dma_active ? xact_aw_addr : 9'b0);
   assign actual_wr_data = internal_wr_active ? i_internal_wr_data : (dma_active ? xact_w_din_processed : 256'b0);
   assign actual_wstrb   = internal_wr_active ? i_internal_wr_strobe : (dma_active ? xact_wstrb : 32'h0); // Use byte strobes from packer
   
   // Output read data to FSM (registered, matches BRAM latency)
   always_ff @(posedge i_clk) begin
       if (!i_reset_n) begin
           o_internal_rd_data <= 256'b0;
       end else begin
           o_internal_rd_data <= xact_r_dout; // Direct from BRAM output
       end
   end

   ACX_BRAM72K_SDP 
     #(
       .byte_width             (        8),
       .read_width             (      144),
       .write_width            (      144),
       .outreg_enable          (        1),
       .outreg_sr_assertion    ("clocked")
       ) 
   xact_mem_lo (
    .wrclk                  (i_clk         ),
    .din                    (actual_wr_data[143:0]),
    .we                     (actual_wstrb[17:0]),
    .wren                   (actual_wr_en),
    .wraddr                 ({actual_wr_addr, 5'h00}),
    .wrmsel                 (1'b0),
    .rdclk                  (i_clk),
    .rden                   (actual_rd_en),
    .rdaddr                 ({actual_rd_addr, 5'h00}),
    .rdmsel                 (1'b0),
    .outlatch_rstn          (i_reset_n),
    .outreg_rstn            (i_reset_n),
    .outreg_ce              (1'b1),
    .dout                   (xact_r_dout[143:0]),
    .sbit_error             (xact_sbit_error_0),
    .dbit_error             (xact_dbit_error_0)
   );

   ACX_BRAM72K_SDP 
     #(
       .byte_width             (        8),
       .read_width             (      144),
       .write_width            (      144),
       .outreg_enable          (        1),
       .outreg_sr_assertion    ("clocked")
       ) 
   xact_mem_hi (
    .wrclk                  (i_clk),
    .din                    ({32'h0, actual_wr_data[255:144]}),
    .we                     ({4'h0, actual_wstrb[31:18]}),
    .wren                   (actual_wr_en),
    .wraddr                 ({actual_wr_addr, 5'h00}),
    .wrmsel                 (1'b0),
    .rdclk                  (i_clk),
    .rden                   (actual_rd_en),
    .rdaddr                 ({actual_rd_addr, 5'h00}),
    .rdmsel                 (1'b0),
    .outlatch_rstn          (i_reset_n),
    .outreg_rstn            (i_reset_n),
    .outreg_ce              (1'b1),
    .dout                   ({dummy_dout, xact_r_dout[255:144]}),
    .sbit_error             (xact_sbit_error_1),
    .dbit_error             (xact_dbit_error_1)
   );


    // If new value read, then store in pipeline
    logic hold_read_d1;
    always@(posedge i_clk)
    begin
        hold_read_d1 <= hold_read;
        if (xact_rd_avail[1] & !hold_read_d1)
        begin
            xact_r_dout_d1 <= xact_r_dout;
            xact_r_dout_d2 <= xact_r_dout_d1;
        end
     end

    // Same pipeline logic for rlast
    // BRAM has a delay of 2 as output register enabled
    always@(posedge i_clk)
    begin
        xact_r_last_dout_q <= ~(|(xact_ar_len[5:0]));
        xact_r_last_dout   <= xact_r_last_dout_q;
    end
        
    always@(posedge i_clk)
    begin
        if (xact_rd_avail[1] & !hold_read_d1)
        begin
            xact_r_last_d1 <= xact_r_last_dout;
            xact_r_last_d2 <= xact_r_last_d1;
        end
     end

    logic valid_not_ready_q;
    logic valid_not_ready;
    logic valid_not_ready_d1;

    assign valid_not_ready_q = (!axi_if_mas.rready & axi_if_mas.rvalid);

    always@(posedge i_clk)
    begin
        valid_not_ready    <= valid_not_ready_q;
        valid_not_ready_d1 <= valid_not_ready;
    end

    // Support ready being deasserted for multiple cycles
    always@(posedge i_clk)
    begin
        if(!i_reset_n) // reset
          r_dout_valid <= 2'b00;
        else
            case ({valid_not_ready_d1, valid_not_ready, valid_not_ready_q})
                3'b000 : r_dout_valid <= 2'b00;
                3'b001 : r_dout_valid <= 2'b01;
                3'b010 : r_dout_valid <= 2'b01;
                3'b011 : r_dout_valid <= 2'b11;
                3'b100 : r_dout_valid <= 2'b00;
                3'b101 : r_dout_valid <= 2'b01;
                3'b110 : r_dout_valid <= 2'b01;
                3'b111 : r_dout_valid <= 2'b11;
            endcase
    end
   
   //-----------------------------------
   // Process read transaction
   // Aquire the ID, address, length and burst type. 
   // Ignore burst size, lock, and qos signals
   //
   // Send read data in response
   //
   // Module uses a BRAM to store write
   // data and read back the read data, using the address
   //
   // Uses a state machine to track the transaction until complete
   //-----------------------------------
   enum  {RD_IDLE, RD_CAPTURE, RD_SEND} rd_xact_state;   
   
   //------------------------------------------------
   // State machine for processing read transactions
   //------------------------------------------------
   always@(posedge i_clk)
     begin
        xact_read_valid_d <= xact_read_valid;
        if(!i_reset_n) // reset
        begin
          rd_xact_state      <= RD_IDLE;
          xact_read_valid    <= 1'b0;
          axi_if_mas.arready <= 1'b0;
        end
        else 
          begin
             case (rd_xact_state)
               RD_IDLE: // wait for the next transaction
                 begin
                    if(axi_if_mas.arvalid && axi_if_mas.arready) // both ready and valid
                    begin
                      rd_xact_state <= RD_CAPTURE;
                      // Assert read_valid, even if in the next stage it is held until write is complete
                      // Indicates to write state machine that a read is pending
                      xact_read_valid    <= 1'b1;
                      // This must be deasserted on the same cycle as AR is registered
                      axi_if_mas.arready <= 1'b0;
                    end
                    else // wait until valid transaction
                    begin
                      rd_xact_state      <= RD_IDLE;
                      // Only assert ready when previous transaction is complete
                      // Otherwise new transaction values get registered, (rid, len), which could corrupt
                      // existing transaction
                      axi_if_mas.arready <= ~( |xact_rd_avail);
                    end
                 end
               RD_CAPTURE: // capture the signals, check there is no conflict with write
                 begin // burst is 16 at most, check if bursts can overlap.  If so, and write occuring, then wait
                    if( ((xact_ar_addr[8:4] == xact_aw_addr[8:4]) &&  xact_write_valid)  || // conflict detected
                          xact_rd_avail[1] )                                                // Existing transaction
                      rd_xact_state <= RD_CAPTURE;  // Wait until above conditions are cleared
                    else // perform the read
                      rd_xact_state <= RD_SEND;
                 end
               RD_SEND: // send out read until burst is complete
                 begin
                    if((xact_ar_len == 6'h00) && axi_if_mas.rready) // read full burst
                    begin
                      xact_read_valid    <= 1'b0;
                      rd_xact_state      <= RD_IDLE;
                    end
                    else // keep reading
                      rd_xact_state <= RD_SEND;
                 end
               default: rd_xact_state <= RD_IDLE;
             endcase // case (rd_xact_state)
          end // else: !if(!i_reset_n)
     end // always@ (posedge i_clk)

   assign xact_rd_en = (rd_xact_state == RD_SEND);

   // Create pipe to determine when read data is available
   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          xact_rd_avail[1:0] <= 2'b00;
        else if( axi_if_mas.rready | ~axi_if_mas.rvalid ) // don't shift if holding
          xact_rd_avail[1:0] <= {xact_rd_avail[0], xact_rd_en};
     end


   // Monitor for any read conflict
   // Does not drive any loads, but was featuring in critical path.
   // Remove from synthesised designs for clarity
   // synthesis synthesis_off
   assign read_conflict = ((xact_ar_addr[8:4] == xact_aw_addr[8:4]) &&
                           (rd_xact_state == RD_CAPTURE) &&
                           xact_write_valid);
   // synthesis synthesis_on


   //--------------------------------
   // Register the transaction signals
   //--------------------------------
   always@(posedge i_clk)
     begin
        hold_read <= 1'b0;
        if(!i_reset_n) // reset
          begin
             xact_ar_addr <= {AXI4_RESPONDER_ADDR_WIDTH{1'b0}};  // AR transaction address
          end
        else if(axi_if_mas.arready && axi_if_mas.arvalid) // capture transaction signals from NAP
          begin
             xact_ar_addr <= axi_if_mas.araddr[13:5]; // AR transaction starting address
          end
        else if(rd_xact_state == RD_SEND)
        begin
          // If reading, and about to assert rvalid, if not ready, then hold address
          // Stops hold of address if ready deasserted before valid is asserted, (whilst pipeline is being populated)
          if( !axi_if_mas.rready & axi_if_mas.rvalid ) 
          begin
            hold_read <= 1'b1;
            xact_ar_addr <= xact_ar_addr; // hold address
          end
          else
          begin
             xact_ar_addr <= xact_ar_addr + 1; // increment address
          end
        end
     end // always@ (posedge i_clk)

   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          begin
             xact_ar_len <= 6'h00;   // AR transaction length, limit of 16
          end
        else if(axi_if_mas.arready && axi_if_mas.arvalid) // capture transaction signals from NAP
          begin
             xact_ar_len <= axi_if_mas.arlen;   // length of read burst
          end
        else if((rd_xact_state == RD_SEND) && (|(xact_ar_len[5:0])) && !(!axi_if_mas.rready & axi_if_mas.rvalid)) // still have more burst reads
          begin
             xact_ar_len <= xact_ar_len - 'd1; // decrement after read
          end
     end // always@ (posedge i_clk)

   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          begin
             xact_ar_id <= {AXI4_ID_WIDTH{1'b0}}; // AR transaction ID
             xact_ar_burst <= 2'b00; // burst type for AR transaction
          end
        else if(axi_if_mas.arready && axi_if_mas.arvalid) // capture transaction signals from NAP
          begin
             xact_ar_id <= axi_if_mas.arid; // AR transaction ID
             xact_ar_burst <= axi_if_mas.arburst; // type of read burst
          end
     end // always@ (posedge i_clk)

   // flop the length counter to match with read output
   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          begin
             xact_ar_len_d1 <= 4'h0;
             xact_ar_len_d2 <= 4'h0;
          end
        else if( !hold_read_d1 ) 
          begin
             // only need 4 bits since length can only be 16 beats
             xact_ar_len_d1 <= xact_ar_len[3:0];
             xact_ar_len_d2 <= xact_ar_len_d1;
          end
     end // always@ (posedge i_clk)

   // Drive read output signals
   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          begin
             axi_if_mas.rvalid <= 1'b0;
          end
        else if(!axi_if_mas.rready & axi_if_mas.rvalid) // not ready, hold values
          begin
             axi_if_mas.rresp <= axi_if_mas.rresp;
             axi_if_mas.rid <= axi_if_mas.rid;
             axi_if_mas.rvalid <= axi_if_mas.rvalid;
          end // if (!axi_if_mas.rready)
        else if(xact_rd_avail[1] && (xact_ar_len_d2 == 4'h0)) // the data is valid, and last data
          begin
             axi_if_mas.rresp <= 2'b00; // response is ok
             axi_if_mas.rid <= xact_ar_id;
             axi_if_mas.rvalid <= 1'b1;
          end // if (xact_rd_avail[1] && (xact_ar_len_d2 == 4'h0))
        else if(xact_rd_avail[1]) // send out read
          begin
             axi_if_mas.rresp <= 2'b00; // response is ok
             axi_if_mas.rid <= xact_ar_id;
             axi_if_mas.rvalid <= 1'b1;
          end // if (xact_rd_avail[1])
        else
          axi_if_mas.rvalid <= 1'b0;
     end // always@ (posedge i_clk)

   // Drive output read data
   always@(posedge i_clk)
     begin
        if(!axi_if_mas.rready & axi_if_mas.rvalid) // not ready, hold values
          begin
             axi_if_mas.rdata <= axi_if_mas.rdata;
          end // if (!axi_if_mas.rready)
        else //if(xact_rd_avail[1])
          begin // grab the valid flopped data
             case(r_dout_valid[1:0])
               2'b01: axi_if_mas.rdata <= xact_r_dout_d1;
               2'b11: axi_if_mas.rdata <= xact_r_dout_d2;
               default: axi_if_mas.rdata <= xact_r_dout;
             endcase // case (r_dout_valid[1:0])
          end
     end // always@ (posedge i_clk)

   // Same flow for rlast
   always@(posedge i_clk)
     begin
        if(!axi_if_mas.rready & axi_if_mas.rvalid) // not ready, hold values
          begin
             axi_if_mas.rlast <= axi_if_mas.rlast;
          end // if (!axi_if_mas.rready)
        else //if(xact_rd_avail[1])
          begin // grab the valid flopped data
             case(r_dout_valid[1:0])
               2'b01: axi_if_mas.rlast <= xact_r_last_d1;
               2'b11: axi_if_mas.rlast <= xact_r_last_d2;
               default: axi_if_mas.rlast <= xact_r_last_dout;
             endcase // case (r_dout_valid[1:0])
          end
     end // always@ (posedge i_clk)

   //-------------------------------------------------
   // Process write transaction
   // Acquire the ID, address, length and burst type. 
   // Ignore burst size, lock and qos signals
   //
   // Write the data and send out the write response
   //
   // Module uses a BRAM to store write data and read back the read
   // data, using the address
   //
   // Uses a state machine to track the transaction until complete
   //-----------------------------------
   enum  {WR_IDLE, WR_CAPTURE, WR_DATA, WR_RSP} wr_xact_state;
   enum  {AW_IDLE, AW_CAPTURED} aw_xact_state;
   
    //------------------------------------------------
    // Address machine for processing write addresses, (AW channel)
    //------------------------------------------------
    // Note that the associated write cycle can be before or after the
    // associated AW cycle.  The W cycle does not have an ID value, hence
    // there cannot be another W cycle until there is an associated AW cycle
    // The W and AW cycles are separate channels, but they can be controlled
    // from the responder using the ready signals
    
    assign aw_registered = (axi_if_mas.awvalid && axi_if_mas.awready);
    assign w_registered  = (axi_if_mas.wvalid && axi_if_mas.wready);
    assign b_registered  = (axi_if_mas.bvalid && axi_if_mas.bready);
    
    always@(posedge i_clk)
    begin
        if(!i_reset_n) // reset
        begin
            aw_xact_state      <= AW_IDLE;
            axi_if_mas.awready <= 1'b0;
        end
        else
        begin
            case (aw_xact_state)
                AW_IDLE : begin
                    axi_if_mas.awready <= 1'b1;
                    if( aw_registered )
                    begin
                        aw_xact_state <= AW_CAPTURED;
                        // Deassert ready until we have sent the write response, (B)
                        // This will prevent overlapping transactions
                        axi_if_mas.awready <= 1'b0;
                    end
                end
                AW_CAPTURED : begin
                    if( b_registered )
                    begin
                        aw_xact_state      <= AW_IDLE;
                        axi_if_mas.awready <= 1'b1;
                    end
                end
                default : begin
                    aw_xact_state <= AW_IDLE;
                    axi_if_mas.awready <= 1'b1;
                end
            endcase
        end  
    end          
   
   //------------------------------------------------
   // State machine for processing write transactions, (W channel)
   //------------------------------------------------
   always@(posedge i_clk)
     begin
        xact_write_valid_d <= xact_write_valid;
        if(!i_reset_n) // reset
        begin
          wr_xact_state <= WR_IDLE;
          xact_write_valid  <= 1'b0;
          aw_sequence_error <= 1'b0;
          axi_if_mas.wready <= 1'b0;
        end
        else 
          begin
             case (wr_xact_state)
               WR_IDLE: // wait for the next transaction
                 begin
                    axi_if_mas.wready <= 1'b1;
                    if (w_registered)
                    begin
                        if ( aw_registered || (aw_xact_state == AW_CAPTURED) )
                        begin
                            // Starting a valid write sequence, this will block reads
                            xact_write_valid <= 1'b1;
                            if ( axi_if_mas.wlast )
                            begin
                                // Single cycle write
                                wr_xact_state <= WR_DATA;
                                axi_if_mas.wready <= 1'b0;
                            end
                            else
                                // Multi-beat write
                                wr_xact_state <= WR_CAPTURE;
                        end
                        else // Error condidtion, AW must be aligned with or before W
                        begin
                            $error("%t : AW not present on first W", $time);
                            aw_sequence_error <= 1'b1;
                        end
                    end
                    else // wait until valid W transaction
                        wr_xact_state <= WR_IDLE;
                 end
               WR_CAPTURE: // capture the address signals, check there is no conflict with read
                 begin // burst is 16 at most, check if top address matches at all
                    if((xact_ar_addr[8:4] == xact_aw_addr[8:4]) &&
                       xact_read_valid & xact_read_valid_d)  // Only hold for conflict if read is not in RD_CAPTURE.
                    begin
                       wr_xact_state     <= WR_CAPTURE;
                       axi_if_mas.wready <= 1'b0;
                    end
                    else
                    begin
                        wr_xact_state     <= WR_DATA;
                        // If last word in deassert ready.
                        if (w_registered & axi_if_mas.wlast)
                          axi_if_mas.wready <= 1'b0;    // Finished transfer
                        else
                          axi_if_mas.wready <= 1'b1;
                    end
                 end
               WR_DATA: // write data into BRAM until burst is complete
                 begin
                    if(xact_wlast && !write_conflict) // write full burst
                    begin
                      wr_xact_state <= WR_RSP;
                      // Stopped writing to memory, read burst can commence if required
                      xact_write_valid <= 1'b0;
                    end
                    else // keep reading
                    begin
                      wr_xact_state <= WR_DATA;
                    end
                    // If either the last word in, or the last transfer, (which results in a change of state)
                    // then if there is not a hold due to a write_conflict, deassert ready.
                    if (((w_registered & axi_if_mas.wlast) || xact_wlast) & ~write_conflict)
                      axi_if_mas.wready <= 1'b0;    // Finished transfer
                    else
                      axi_if_mas.wready <= ~write_conflict;
                 end
               WR_RSP: // send out the write response
                 begin
                    if(b_registered) // Response received
                    begin
                      wr_xact_state     <= WR_IDLE;
                      axi_if_mas.wready <= 1'b1;
                    end
                    else // wait for ready
                    begin
                      wr_xact_state     <= WR_RSP;
                      axi_if_mas.wready <= 1'b0;
                    end
                 end
               default: wr_xact_state <= WR_IDLE;
             endcase // case (wr_xact_state)
          end // else: !if(!i_reset_n)
     end // always@ (posedge i_clk)

   // Do assignment conflict at the start of a burst, once a write burst has started, the read burst is blocked
   assign write_conflict = 1'b0;

   //--------------------------------------------------------------------
   // Data Path Logic - Direct Pass-Through
   //--------------------------------------------------------------------
   // Legacy processing removed - data passes through unchanged
   // Maintaining interface compatibility for existing connections
   always_comb begin
       xact_w_din_processed = xact_w_din; // Direct pass-through (processing disabled)
   end

   //------------------------------------
   // Capture transaction signals
   //------------------------------------

   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          begin
             xact_aw_id       <= {AXI4_ID_WIDTH{1'b0}};             // AW transaction ID
             xact_aw_addr     <= {AXI4_RESPONDER_ADDR_WIDTH{1'b0}}; // AW transaction address
             xact_aw_len      <= 8'h00;                             // AW transaction length, limit of 16
             xact_aw_burst    <= 2'b00;                             // burst type for AR transaction
          end
        else if(aw_registered) // Capture AW signals from NAP
          begin
             xact_aw_id       <= axi_if_mas.awid;               // AW transaction ID
             xact_aw_addr     <= axi_if_mas.awaddr[13:5];       // AW transaction starting address
             xact_aw_len      <= axi_if_mas.awlen;              // Length of write burst
             xact_aw_burst    <= axi_if_mas.awburst;            // Type of write burst
          end
        else if(xact_wr_en) // still have more burst writes
          begin
             xact_aw_addr <= xact_aw_addr + 1;
          end
     end // always@ (posedge i_clk)


   // Capture write data
   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          begin
             xact_wr_en <= 1'b0;
             xact_wstrb <= 32'h0;
             xact_wlast <= 1'b0;
          end
        else if(w_registered)       // Valid data write
          begin
             xact_wr_en <= 1'b1;
             xact_wstrb <= axi_if_mas.wstrb;
             xact_wlast <= axi_if_mas.wlast;
             xact_w_din <= axi_if_mas.wdata;
          end
        else if(write_conflict) // there is write conflict
          begin // hold the data, don't write it
             xact_wr_en <= 1'b0;
             xact_wstrb <= xact_wstrb;
             xact_wlast <= xact_wlast;
             xact_w_din <= xact_w_din;
          end
        else if(xact_wlast)
          begin
             xact_wr_en <= 1'b1; // write last data
             xact_wstrb <= 32'h0;
             xact_wlast <= 1'b0;
          end
        else
          begin
             xact_wr_en <= 1'b0;
             xact_wstrb <= 32'h0;
             xact_wlast <= 1'b0;
          end  
     end // always@ (posedge i_clk)

   // Drive write response signals
   always@(posedge i_clk)
     begin
        if(!i_reset_n) // reset
          begin
             axi_if_mas.bvalid <= 1'b0;
          end
        else if((wr_xact_state == WR_RSP) & ~b_registered) // Issue write response, (B channel)
          begin
             axi_if_mas.bvalid <= 1'b1;
             axi_if_mas.bid <= xact_aw_id;
             axi_if_mas.bresp <= 2'b00;
          end
        else
          begin
             axi_if_mas.bvalid <= 1'b0;
          end
     end // always@ (posedge i_clk)

`ifdef ACX_USE_SNAPSHOT

    ACX_PROBE_POINT #(
        .width  (12),
        .tag    (PROBE_NAME)
    ) x_probe_snapshot (
        .din({
            axi_if_mas.rlast,  axi_if_mas.rready,  axi_if_mas.rvalid,
            axi_if_mas.arready, axi_if_mas.arvalid,
            axi_if_mas.bready,  axi_if_mas.bvalid,
            axi_if_mas.wlast,  axi_if_mas.wready,  axi_if_mas.wvalid,
            axi_if_mas.awready, axi_if_mas.awvalid
            })
    );

`endif
   
endmodule : dma_bram_bridge

