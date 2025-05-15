/*
 * Copyright © 2024 Chris Keilbart
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module core_arbiter

    #(
        parameter logic INCLUDE_DCACHE = 1'b1,
        parameter logic INCLUDE_ICACHE = 1'b1,
        parameter logic INCLUDE_MMUS = 1'b1
    ) (
        input logic clk,
        input logic rst,

        //mem_interface.rw_slave dcache,
        slave_rw_mem_interface_input dcache_input;
        slave_rw_mem_interface_output dcache_output;
        
        //mem_interface.ro_slave icache,
        slave_ro_mem_interface_input icache_input;
        slave_ro_mem_interface_output icache_output;
        
        //mem_interface.ro_slave dmmu,
        slave_ro_mem_interface_input dmmu_input,
        slave_ro_mem_interface_output dmmu_output,
        
        //mem_interface.ro_slave immu,
        slave_ro_mem_interface_input immu_input,
        slave_ro_mem_interface_output immu_output,
        
        //mem_interface.mem_master mem
        master_ro_mem_interface_input mem_input,
        master_ro_mem_interface_output mem_output
    );

    //Multiplexes memory requests and demultiplexes memory responses
    //If the MMUs are not present the MSB of the memory ID is always 0
    //If the I$ is also not present the entire ID can be set to 0

    logic[3:0] request;
    logic[3:0][31:2] addr;
    logic[3:0][4:0] rlen;
    logic[3:0] rnw;
    logic[3:0] rmw;
    logic[1:0] port;

    ////////////////////////////////////////////////////
    //Implementation

    //D$
    assign request[0] = INCLUDE_DCACHE ? dcache_input.request : 0;
    assign addr[0] = INCLUDE_DCACHE ? dcache_input.addr : 'x;
    assign rlen[0] = INCLUDE_DCACHE ? dcache_input.rlen : 'x;
    assign rnw[0] = INCLUDE_DCACHE ? dcache_input.rnw : 'x;
    assign rmw[0] = INCLUDE_DCACHE ? dcache_input.rmw : 'x;
    assign mem_output.wbe = dcache_input.wbe;
    assign mem_output.wdata = dcache_input.wdata;
    assign dcache_output.inv = mem_input.inv;
    assign dcache_output.inv_addr = mem_input.inv_addr;
    assign dcache_output.write_outstanding = mem_input.write_outstanding;
    assign dcache_output.ack = mem_input.ack & port == 2'b00;
    assign dcache_output.rvalid = mem_input.rvalid & mem.rid == 2'b00;
    assign dcache_output.rdata = mem_input.rdata;
    //I$
    assign request[1] = INCLUDE_ICACHE ? icache_intput.request : 0;
    assign addr[1] = INCLUDE_ICACHE ? icache_intput.addr : 'x;
    assign rlen[1] = INCLUDE_ICACHE ? icache_intput.rlen : 'x;
    assign rnw[1] = INCLUDE_ICACHE ? 1 : 'x;
    assign rmw[1] = INCLUDE_ICACHE ? 0 : 'x;
    assign icache_output.ack = mem.ack & port == 2'b01;
    assign icache_output.rvalid = mem.rvalid & mem.rid == 2'b01;
    assign icache_output.rdata = mem.rdata;
    //DMMU
    assign request[2] = INCLUDE_MMUS ? dmmu_input.request : 0;
    assign addr[2] = INCLUDE_MMUS ? dmmu_input.addr : 'x;
    assign rlen[2] = INCLUDE_MMUS ? dmmu_input.rlen : 'x;
    assign rnw[2] = INCLUDE_MMUS ? 1 : 'x;
    assign rmw[2] = INCLUDE_MMUS ? 0 : 'x;
    assign dmmu_output.rdata = mem_input.rdata;
    assign dmmu_output.ack = mem_input.ack & port == 2'b10;
    assign dmmu_output.rvalid = mem_input.rvalid & mem.rid == 2'b10;
    //IMMU
    assign request[3] = INCLUDE_MMUS ? immu_input.request : 0;
    assign addr[3] = INCLUDE_MMUS ? immu_input.addr : 'x;
    assign rlen[3] = INCLUDE_MMUS ? immu_input.rlen : 'x;
    assign rnw[3] = INCLUDE_MMUS ? 1 : 'x;
    assign rmw[3] = INCLUDE_MMUS ? 0 : 'x;
    assign immu_output.rdata = mem_input.rdata;
    assign immu_output.ack = mem_input.ack & port == 2'b11;
    assign immu_output.rvalid = mem_input.rvalid & mem.rid == 2'b11;

    
    ////////////////////////////////////////////////////
    //Arbitration
    round_robin #(.NUM_PORTS(4)) rr (
        .requests(request),
        .grant(mem_input.request & mem_input.ack),
        .grantee(port),
    .*);

    assign mem_output.request = |request;
    assign mem_output.addr = addr[port];
    assign mem_output.rlen = rlen[port];
    assign mem_output.rnw = rnw[port];
    assign mem_output.rmw = rmw[port];
    assign mem_output.id = port;

endmodule
