/*
 * Copyright © 2017 Eric Matthews, Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module local_mem_sub_unit

    import riscv_types::*;

    (
        input logic clk,
        input logic rst,

        output logic write_outstanding,
        input logic amo,
        input amo_t amo_type,
        //amo_interface.subunit amo_unit,
        subunit_amo_interface_input amo_unit_input,
        subunit_amo_interface_output amo_unit_output,
        
        //memory_sub_unit_interface.responder unit,
        responder_memory_sub_unit_interface_input unit_input,
        responder_memory_sub_unit_interface_output unit_output,
        
        //local_memory_interface.master local_mem
        master_local_memory_interface_input local_mem_input,
        master_local_memory_interface_output local_mem_output
    );

    //If amo is tied to 0 and amo_unit is disconnected the tools can optimize most of the logic away

    logic rmw;
    logic[31:2] rmw_addr;
    logic[31:0] rmw_rs2;
    amo_t rmw_op;
    logic sc_valid;
    logic sc_valid_r;
    
    assign write_outstanding = 0;

    assign sc_valid = amo & amo_type == AMO_SC_FN5 & amo_unit_input.reservation_valid;
    assign amo_unit_output.set_reservation = unit_input.new_request & amo & amo_type == AMO_LR_FN5;
    assign amo_unit_output.clear_reservation = unit_input.new_request;
    assign amo_unit_output.reservation = unit_input.addr;

    assign amo_unit_output.rmw_valid = rmw;
    assign amo_unit_output.op = rmw_op;
    assign amo_unit_output.rs1 = local_mem_input.data_out;
    assign amo_unit_output.rs2 = rmw_rs2;

    always_comb begin
        if (rmw) begin
            unit_output.ready = 0;
            local_mem_output.addr = rmw_addr;
            local_mem_output.en = 1;
            local_mem_output.be = '1;
            local_mem_output.data_in = amo_unit_input.rd;
            unit_output.data_out = local_mem_input.data_out;
        end else begin
            unit_output.ready = 1;
            local_mem_output.addr = unit_input.addr[31:2];
            local_mem_output.en = unit_input.new_request;
            local_mem_output.be = {4{unit_input.we | sc_valid}} & unit_input.be; //SC only writes when it succeeds
            local_mem_output.data_in = unit_input.data_in;
            unit_output.data_out = sc_valid_r ? 32'b1 : local_mem_input.data_out;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            unit_output.data_valid <= 0;
            rmw <= 0;
            sc_valid_r <= 0;
        end
        else begin
            unit_output.data_valid <= unit_input.new_request & unit_input.re;
            rmw <= unit_input.new_request & amo & ~(amo_type inside {AMO_LR_FN5, AMO_SC_FN5});
            sc_valid_r <= sc_valid;
        end
        rmw_addr <= unit_input.addr[31:2];
        rmw_rs2 <= unit_input.data_in;
        rmw_op <= amo_type;
    end

endmodule
