/*
 * Copyright © 2024 Eric Matthews, Chris Keilbart, Lesley Shannon
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
`include "external_interfaces.sv"
module axi_master

    import riscv_types::*;

    (
        input logic clk,
        input logic rst,

        output logic write_outstanding,
        //axi_interface.master m_axi,
        input master_axi_interface_input m_axi_input,
        output master_axi_interface_output m_axi_output,

        input logic amo,
        input amo_t amo_type,
        //amo_interface.subunit amo_unit,
        subunit_amo_interface_input amo_unit_input,
        subunit_amo_interface_output amo_unit_output,
        
        //memory_sub_unit_interface.responder ls
        responder_memory_sub_unit_interface_input ls_input,
        responder_memory_sub_unit_interface_output ls_output
    );

    ////////////////////////////////////////////////////
    //Implementation
    typedef enum {
        READY,
        REQUESTING_WRITE,
        REQUESTING_READ,
        REQUESTING_AMO_M,
        WAITING_READ,
        WAITING_WRITE
    } state_t;
    state_t current_state;

    logic request_is_invalid_sc;
    assign request_is_invalid_sc = amo & amo_type == AMO_SC_FN5 & ~amo_unit_input.reservation_valid;

    assign amo_unit_output.set_reservation = ls_input.new_request & amo & amo_type == AMO_LR_FN5;
    assign amo_unit_output.clear_reservation = ls_input.new_request;
    assign amo_unit_output.reservation = ls_input.addr;
    assign amo_unit_output.rs1 = ls_output.data_out;

    logic[29:0] addr;
    assign m_axi_output.awaddr = {addr, 2'b0};
    assign m_axi_output.araddr = {addr, 2'b0};
    assign m_axi_output.awlen = '0;
    assign m_axi_output.arlen = '0;
    assign m_axi_output.awburst = '0;
    assign m_axi_output.arburst = '0;
    assign m_axi_output.awid = '0;
    assign m_axi_output.arid = '0;
    assign m_axi_output.rready = 1;
    assign m_axi_output.bready = 1;

    always_ff @(posedge clk) begin
        unique case (current_state)
            READY : begin //Accept any request
                ls_output.ready <= ~ls_input.new_request | request_is_invalid_sc;
                ls_output.data_out <= 1;
                ls_output.data_valid <= ls_input.new_request & request_is_invalid_sc;
                addr <= ls_input.addr[31:2];
                m_axi_output.awlock <= amo & amo_type != AMO_LR_FN5; //Used in WAITING_READ to determine if it was a RMW
                m_axi_output.awvalid <= ls_input.new_request & (ls_input.we | (amo & amo_type == AMO_SC_FN5 & amo_unit_input.reservation_valid));
                m_axi_output.arlock <= amo & amo_type != AMO_SC_FN5; //Used in WAITING_WRITE to determine if it was a RNW
                m_axi_output.arvalid <= ls_input.new_request & ls_input.re & ~(amo & amo_type == AMO_SC_FN5);
                m_axi_output.wvalid <= ls_input.new_request & (ls_input.we | (amo & amo_type == AMO_SC_FN5 & amo_unit_input.reservation_valid));
                m_axi_output.wdata <= ls_input.data_in;
                m_axi_output.wstrb <= ls_input.be;
                write_outstanding <= ls_input.new_request & (ls_input.we | amo);
                amo_unit_output.rmw_valid <= 0;
                amo_unit_output.op <= amo_type;
                amo_unit_output.rs2 <= ls_input.data_in; //Cannot use wdata because wdata will be overwritten if the RMW is not exclusive
                if (ls_input.new_request & (ls_input.we | (amo & amo_type == AMO_SC_FN5 & amo_unit_input.reservation_valid)))
                    current_state <= REQUESTING_WRITE;
                else if (ls_input.new_request & ~request_is_invalid_sc)
                    current_state <= REQUESTING_READ;
            end
            REQUESTING_READ : begin //Wait for read to be accepted
                m_axi_output.arvalid <= ~m_axi_input.arready;
                if (m_axi_input.arready)
                    current_state <= WAITING_READ;
            end
            WAITING_READ : begin //Wait for read response
                ls_output.ready <= m_axi_input.rvalid & ~m_axi_output.awlock;
                ls_output.data_out <= m_axi_input.rdata;
                ls_output.data_valid <= m_axi_input.rvalid;
                amo_unit_output.rmw_valid <= m_axi_input.rvalid;
                if (m_axi_input.rvalid)
                    current_state <= m_axi_output.awlock ? REQUESTING_AMO_M : READY;
            end
            REQUESTING_AMO_M : begin //One cycle for computing the AMO write value
                ls_output.data_valid <= 0;
                m_axi_output.awvalid <= 1;
                m_axi_output.wvalid <= 1;
                m_axi_output.wdata <= amo_unit_input.rd;
                amo_unit_output.rmw_valid <= 0;
                current_state <= REQUESTING_WRITE;
            end
            REQUESTING_WRITE : begin //Wait for write (address and data) to be accepted
                m_axi_output.awvalid <= m_axi_output.awvalid & ~m_axi_input.awready;
                m_axi_output.wvalid <= m_axi_output.wvalid & ~m_axi_input.wready;
                if ((~m_axi_output.awvalid | m_axi_input.awready) & (~m_axi_output.wvalid | m_axi_input.wready))
                    current_state <= WAITING_WRITE;
            end
            WAITING_WRITE : begin //Wait for write response; resubmit if RMW was not exclusive
                ls_output.ready <= m_axi_input.bvalid & (~m_axi_output.arlock | m_axi_input.bresp == 2'b01);
                ls_output.data_out <= {31'b0, m_axi_input.bresp != 2'b01};
                ls_output.data_valid <= m_axi_input.bvalid & m_axi_output.awlock & ~m_axi_output.arlock;
                m_axi_output.arvalid <= m_axi_input.bvalid & m_axi_output.arlock & m_axi_input.bresp != 2'b01;
                write_outstanding <= ~(m_axi_input.bvalid & (~m_axi_output.arlock | m_axi_input.bresp == 2'b01));
                if (m_axi_input.bvalid)
                    current_state <= m_axi_output.arlock & m_axi_input.bresp != 2'b01 ? REQUESTING_READ : READY;
            end
        endcase
        if (rst)
            current_state <= READY;
    end

endmodule
