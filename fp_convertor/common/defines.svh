`ifndef DEFINES_SVH
`define DEFINES_SVH

`define pack2d_i(in, num, width) \
    logic [num-1:0][width-1:0] ``in``_li; \
    always_comb begin: rof_pack_``in``_i \
        for (int i = 0; i < num; i++) begin \
            ``in``_li[i] = ``in``_i[(i * width) +: width]; \
        end \
    end

`define pack2d_o(out, num, width) \
    logic [num-1:0][width-1:0] ``out``_lo; \
    always_comb begin: rof_pack_``out``_o \
        for (int i = 0; i < num; i++) begin \
            ``out``_o[(i * width) +: width] = ``out``_lo[i]; \
        end \
    end

`define declare_axi_master_port(name, addr_width, data_width, id_width, resp_width, len_width, size_width, burst_width) \
    input logic ``name``_arready_i, \
    output logic ``name``_arvalid_o, \
    output logic [addr_width-1:0] ``name``_araddr_o, \
    output logic [id_width-1:0] ``name``_arid_o, \
    output logic [len_width-1:0] ``name``_arlen_o, \
    output logic [size_width-1:0] ``name``_arsize_o, \
    output logic [burst_width-1:0] ``name``_arburst_o, \
    output logic ``name``_rready_o, \
    input logic ``name``_rvalid_i, \
    input logic ``name``_rlast_i, \
    input logic [data_width-1:0] ``name``_rdata_i, \
    input logic [id_width-1:0] ``name``_rid_i, \
    input logic [resp_width-1:0] ``name``_rresp_i, \
    input logic ``name``_awready_i, \
    output logic ``name``_awvalid_o, \
    output logic [addr_width-1:0] ``name``_awaddr_o, \
    output logic [id_width-1:0] ``name``_awid_o, \
    output logic [len_width-1:0] ``name``_awlen_o, \
    output logic [size_width-1:0] ``name``_awsize_o, \
    output logic [burst_width-1:0] ``name``_awburst_o, \
    input logic ``name``_wready_i, \
    output logic ``name``_wvalid_o, \
    output logic ``name``_wlast_o, \
    output logic [data_width-1:0] ``name``_wdata_o, \
    output logic [(data_width/8)-1:0] ``name``_wstrb_o, \
    output logic ``name``_bready_o, \
    input logic ``name``_bvalid_i, \
    input logic [id_width-1:0] ``name``_bid_i, \
    input logic [resp_width-1:0] ``name``_bresp_i

`define declare_axi_slave_port(name, addr_width, data_width, id_width, resp_width, len_width, size_width, burst_width) \
    output logic ``name``_arready_o, \
    input logic ``name``_arvalid_i, \
    input logic [addr_width-1:0] ``name``_araddr_i, \
    input logic [id_width-1:0] ``name``_arid_i, \
    input logic [len_width-1:0] ``name``_arlen_i, \
    input logic [size_width-1:0] ``name``_arsize_i, \
    input logic [burst_width-1:0] ``name``_arburst_i, \
    input logic ``name``_rready_i, \
    output logic ``name``_rvalid_o, \
    output logic ``name``_rlast_o, \
    output logic [data_width-1:0] ``name``_rdata_o, \
    output logic [id_width-1:0] ``name``_rid_o, \
    output logic [resp_width-1:0] ``name``_rresp_o, \
    output logic ``name``_awready_o, \
    input logic ``name``_awvalid_i, \
    input logic [addr_width-1:0] ``name``_awaddr_i, \
    input logic [id_width-1:0] ``name``_awid_i, \
    input logic [len_width-1:0] ``name``_awlen_i, \
    input logic [size_width-1:0] ``name``_awsize_i, \
    input logic [burst_width-1:0] ``name``_awburst_i, \
    output logic ``name``_wready_o, \
    input logic ``name``_wvalid_i, \
    input logic ``name``_wlast_i, \
    input logic [data_width-1:0] ``name``_wdata_i, \
    input logic [(data_width/8)-1:0] ``name``_wstrb_i, \
    input logic ``name``_bready_i, \
    output logic ``name``_bvalid_o, \
    output logic [id_width-1:0] ``name``_bid_o, \
    output logic [resp_width-1:0] ``name``_bresp_o

`define declare_axi_master_port_array_flattened(name, num, addr_width, data_width, id_width, resp_width, len_width, size_width, burst_width) \
    input logic [num-1:0] ``name``_arready_i, \
    output logic [num-1:0] ``name``_arvalid_o, \
    output logic [num*addr_width-1:0] ``name``_araddr_o, \
    output logic [num*id_width-1:0] ``name``_arid_o, \
    output logic [num*len_width-1:0] ``name``_arlen_o, \
    output logic [num*size_width-1:0] ``name``_arsize_o, \
    output logic [num*burst_width-1:0] ``name``_arburst_o, \
    output logic [num-1:0] ``name``_rready_o, \
    input logic [num-1:0] ``name``_rvalid_i, \
    input logic [num-1:0] ``name``_rlast_i, \
    input logic [num*data_width-1:0] ``name``_rdata_i, \
    input logic [num*id_width-1:0] ``name``_rid_i, \
    input logic [num*resp_width-1:0] ``name``_rresp_i, \
    input logic [num-1:0] ``name``_awready_i, \
    output logic [num-1:0] ``name``_awvalid_o, \
    output logic [num*addr_width-1:0] ``name``_awaddr_o, \
    output logic [num*id_width-1:0] ``name``_awid_o, \
    output logic [num*len_width-1:0] ``name``_awlen_o, \
    output logic [num*size_width-1:0] ``name``_awsize_o, \
    output logic [num*burst_width-1:0] ``name``_awburst_o, \
    input logic [num-1:0] ``name``_wready_i, \
    output logic [num-1:0] ``name``_wvalid_o, \
    output logic [num-1:0] ``name``_wlast_o, \
    output logic [num*data_width-1:0] ``name``_wdata_o, \
    output logic [num*(data_width/8)-1:0] ``name``_wstrb_o, \
    output logic [num-1:0] ``name``_bready_o, \
    input logic [num-1:0] ``name``_bvalid_i, \
    input logic [num*id_width-1:0] ``name``_bid_i, \
    input logic [num*resp_width-1:0] ``name``_bresp_i

`define declare_axi_master_port_array_packed(name, num, addr_width, data_width, id_width, resp_width, len_width, size_width, burst_width) \
    input logic [num-1:0] ``name``_arready_i, \
    output logic [num-1:0] ``name``_arvalid_o, \
    output logic [num-1:0][addr_width-1:0] ``name``_araddr_o, \
    output logic [num-1:0][id_width-1:0] ``name``_arid_o, \
    output logic [num-1:0][len_width-1:0] ``name``_arlen_o, \
    output logic [num-1:0][size_width-1:0] ``name``_arsize_o, \
    output logic [num-1:0][burst_width-1:0] ``name``_arburst_o, \
    output logic [num-1:0] ``name``_rready_o, \
    input logic [num-1:0] ``name``_rvalid_i, \
    input logic [num-1:0] ``name``_rlast_i, \
    input logic [num-1:0][data_width-1:0] ``name``_rdata_i, \
    input logic [num-1:0][id_width-1:0] ``name``_rid_i, \
    input logic [num-1:0][resp_width-1:0] ``name``_rresp_i, \
    input logic [num-1:0] ``name``_awready_i, \
    output logic [num-1:0] ``name``_awvalid_o, \
    output logic [num-1:0][addr_width-1:0] ``name``_awaddr_o, \
    output logic [num-1:0][id_width-1:0] ``name``_awid_o, \
    output logic [num-1:0][len_width-1:0] ``name``_awlen_o, \
    output logic [num-1:0][size_width-1:0] ``name``_awsize_o, \
    output logic [num-1:0][burst_width-1:0] ``name``_awburst_o, \
    input logic [num-1:0] ``name``_wready_i, \
    output logic [num-1:0] ``name``_wvalid_o, \
    output logic [num-1:0] ``name``_wlast_o, \
    output logic [num-1:0][data_width-1:0] ``name``_wdata_o, \
    output logic [num-1:0][(data_width/8)-1:0] ``name``_wstrb_o, \
    output logic [num-1:0] ``name``_bready_o, \
    input logic [num-1:0] ``name``_bvalid_i, \
    input logic [num-1:0][id_width-1:0] ``name``_bid_i, \
    input logic [num-1:0][resp_width-1:0] ``name``_bresp_i


`define declare_axil_slave_port(name, addr_width, data_width, resp_width) \
    output logic ``name``_arready_o, \
    input logic ``name``_arvalid_i, \
    input logic [addr_width-1:0] ``name``_araddr_i, \
    input logic ``name``_rready_i, \
    output logic ``name``_rvalid_o, \
    output logic [data_width-1:0] ``name``_rdata_o, \
    output logic [resp_width-1:0] ``name``_rresp_o, \
    output logic ``name``_awready_o, \
    input logic ``name``_awvalid_i, \
    input logic [addr_width-1:0] ``name``_awaddr_i, \
    output logic ``name``_wready_o, \
    input logic ``name``_wvalid_i, \
    input logic [data_width-1:0] ``name``_wdata_i, \
    input logic [(data_width/8)-1:0] ``name``_wstrb_i, \
    input logic ``name``_bready_i, \
    output logic ``name``_bvalid_o, \
    output logic [resp_width-1:0] ``name``_bresp_o

`endif