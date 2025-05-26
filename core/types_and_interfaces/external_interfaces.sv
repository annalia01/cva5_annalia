/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */

    import cva5_config::*;

typedef struct packed {
    logic arvalid;
    logic [31:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic [3:0] arcache;
    logic [5:0] arid;
    logic arlock;

    logic rready;

    logic awvalid;
    logic [31:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic [3:0] awcache;
    logic [5:0] awid;
    logic awlock;

    logic wvalid;
    logic [31:0] wdata;
    logic [3:0] wstrb;
    logic wlast;

    logic bready;
} master_axi_interface_output;

typedef struct packed {
    logic arready;

    logic rvalid;
    logic [31:0] rdata;
    logic [1:0] rresp;
    logic rlast;
    logic [5:0] rid;

    logic awready;
    logic wready;

    logic bvalid;
    logic [1:0] bresp;
    logic [5:0] bid;
} master_axi_interface_input;

typedef struct packed {
    logic arvalid;
    logic [31:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic [3:0] arcache;
    logic [5:0] arid;
    logic arlock;

    logic rready;

    logic awvalid;
    logic [31:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic [3:0] awcache;
    logic [5:0] awid;
    logic awlock;

    logic wvalid;
    logic [31:0] wdata;
    logic [3:0] wstrb;
    logic wlast;

    logic bready;
} slave_axi_interface_input;

typedef struct packed {
    logic arready;

    logic rvalid;
    logic [31:0] rdata;
    logic [1:0] rresp;
    logic rlast;
    logic [5:0] rid;

    logic awready;
    logic wready;

    logic bvalid;
    logic [1:0] bresp;
    logic [5:0] bid;
} slave_axi_interface_output;


typedef struct packed {
    logic [31:0] readdata;
    logic waitrequest;
    logic readdatavalid;
    logic writeresponsevalid;
} master_avalon_interface_input;

typedef struct packed {
    logic [31:0] addr;
    logic read;
    logic write;
    logic lock;
    logic [3:0] byteenable;
    logic [31:0] writedata;
} master_avalon_interface_output;

typedef struct packed {
    logic [31:0] addr;
    logic read;
    logic write;
    logic lock;
    logic [3:0] byteenable;
    logic [31:0] writedata;
} slave_avalon_interface_input;

typedef struct packed {
    logic [31:0] readdata;
    logic waitrequest;
    logic readdatavalid;
    logic writeresponsevalid;
} slave_avalon_interface_output;

typedef struct packed {
    logic [29:0] adr;
    logic [31:0] dat_w;
    logic [3:0] sel;
    logic cyc;
    logic stb;
    logic we;
    logic [2:0] cti;
    logic [1:0] bte;
} master_wishbone_interface_output;

typedef struct packed {
    logic [31:0] dat_r;
    logic ack;
    logic err;
}  master_wishbone_interface_input;

typedef struct packed {
    logic [29:0] adr;
    logic [31:0] dat_w;
    logic  [3:0] sel;
    logic cyc;
    logic stb;
    logic we;
    logic [2:0] cti;
    logic [1:0] bte;
} slave_wishbone_interface_input;

typedef struct packed {
    logic [31:0] dat_r;
    logic ack;
    logic err;
} slave_wishbone_interface_output;

typedef struct packed {
    logic        ack;
    logic        rvalid;
    logic [31:0] rdata;
} master_ro_mem_interface_input;

typedef struct packed {
    logic request;
    logic [31:2] addr;
    logic  [4:0] rlen;
} master_ro_mem_interface_output;

typedef struct packed {
    logic request;
    logic [31:2] addr;
    logic  [4:0] rlen;
} slave_ro_mem_interface_input;

typedef struct packed {
    logic        ack;
    logic        rvalid;
    logic [31:0] rdata;
} slave_ro_mem_interface_output;

typedef struct packed {
    logic        ack;
    logic        rvalid;
    logic [31:0] rdata;
    logic        inv;
    logic [31:2] inv_addr;
    logic        write_outstanding;
} master_rw_mem_interface_input;

typedef struct packed {
    logic        request;
    logic [31:2] addr;
    logic  [4:0] rlen;
    logic        rnw;
    logic        rmw;
    logic  [3:0] wbe;
    logic [31:0] wdata;
} master_rw_mem_interface_output;

typedef struct packed {
    logic        request;
    logic [31:2] addr;
    logic  [4:0] rlen;
    logic        rnw;
    logic        rmw;
    logic  [3:0] wbe;
    logic [31:0] wdata;
} slave_rw_mem_interface_input;

typedef struct packed {
    logic        ack;
    logic        rvalid;
    logic [31:0] rdata;
    logic        inv;
    logic [31:2] inv_addr;
    logic        write_outstanding;
} slave_rw_mem_interface_output;

typedef struct packed {
    logic        ack;
    logic        rvalid;
    logic [31:0] rdata;
    logic  [1:0] rid;
    logic        inv;
    logic [31:2] inv_addr;
    logic        write_outstanding;
} master_mem_mem_interface_input;

typedef struct packed {
    logic        request;
    logic [31:2] addr;
    logic  [4:0] rlen;
    logic        rnw;
    logic        rmw;
    logic  [3:0] wbe;
    logic [31:0] wdata;
    logic  [1:0] id;
} master_mem_mem_interface_output;

typedef struct packed {
    logic        request;
    logic [31:2] addr;
    logic  [4:0] rlen;
    logic        rnw;
    logic        rmw;
    logic  [3:0] wbe;
    logic [31:0] wdata;
    logic  [1:0] id;
} slave_mem_mem_interface_input;

typedef struct packed {
    logic        ack;
    logic        rvalid;
    logic [31:0] rdata;
    logic  [1:0] rid;
    logic        inv;
    logic [31:2] inv_addr;
    logic        write_outstanding;
} slave_mem_mem_interface_output;

typedef struct packed {
    logic [31:0] data_out;
} master_local_memory_interface_input;

typedef struct packed {
    logic [29:0] addr;
    logic        en;
    logic  [3:0] be;
    logic [31:0] data_in;
} master_local_memory_interface_output;

typedef struct packed {
    logic [29:0] addr;
    logic        en;
    logic  [3:0] be;
    logic [31:0] data_in;
} slave_local_memory_interface_input;

typedef struct packed {
    logic [31:0] data_out;
} slave_local_memory_interface_output;


