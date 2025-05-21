/*
 * Copyright © 2019 Eric Matthews, Chris Keilbart, Lesley Shannon
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

module avalon_master

    import riscv_types::*;

    #(
        parameter int unsigned LR_WAIT = 32, //The number of cycles lock is held after an LR
        parameter logic INCLUDE_AMO = 1 //Required because the tools cannot fully optimize even if amo signals are tied off
    )
    (
        input logic clk,
        input logic rst,

        output logic write_outstanding,
        //avalon_interface.master m_avalon,
        master_avalon_interface_input m_avalon_input,
        master_avalon_interface_output m_avalon_output,

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
        REQUESTING,
        REQUESTING_AMO_R,
        REQUESTING_AMO_M,
        REQUESTING_AMO_W,
        READY_LR,
        REQUESTING_SC
    } state_t;
    state_t current_state;

    logic[$clog2(LR_WAIT)-1:0] lock_counter;
    logic request_is_sc;
    assign request_is_sc = amo & amo_type == AMO_SC_FN5;

    assign amo_unit_output.set_reservation = ls_input.new_request & amo & amo_type == AMO_LR_FN5;
    assign amo_unit_output.clear_reservation = ls_input.new_request;
    assign amo_unit_output.reservation = ls_input.addr;
    assign amo_unit_output.rs1 = ls_output.data_out;
    assign amo_unit_output.rs2 = m_avalon_output.writedata;

    always_ff @(posedge clk) begin
        m_avalon_output.addr[1:0] <= '0;
        unique case (current_state)
            READY : begin //Accept any request
                ls_output.ready <= ~ls_input.new_request | request_is_sc;
                ls_output.data_out <= 32'b1;
                ls_output.data_valid <= ls_input.new_request & request_is_sc;
                m_avalon_output.addr[31:2] <= ls_input.addr[31:2];
                m_avalon_output.byteenable <= ls_input.be;
                m_avalon_output.writedata <= ls_input.data_in;
                m_avalon_output.read <= ls_input.new_request & ls_input.re & ~request_is_sc;
                m_avalon_output.write <= ls_input.new_request & ls_input.we;
                m_avalon_output.lock <= ls_input.new_request & amo;
                write_outstanding <= ls_input.new_request & (ls_input.we | amo);
                amo_unit_output.rmw_valid <= 0;
                amo_unit_output.op <= amo_type;
                lock_counter <= '0;
                if (ls_input.new_request & (~amo | amo_type == AMO_LR_FN5))
                    current_state <= REQUESTING;
                else if (ls_input.new_request & amo & amo_type != AMO_SC_FN5)
                    current_state <= REQUESTING_AMO_R;
            end
            REQUESTING : begin //Wait for response
                ls_output.ready <= ~m_avalon_input.waitrequest;
                ls_output.data_out <= m_avalon_input.readdata;
                ls_output.data_valid <= m_avalon_output.read & ~m_avalon_input.waitrequest;
                m_avalon_output.read <= m_avalon_output.read & m_avalon_input.waitrequest;
                m_avalon_output.write <= m_avalon_output.write & m_avalon_input.waitrequest;
                write_outstanding <= m_avalon_output.write & ~m_avalon_input.waitrequest;
                if (~m_avalon_input.waitrequest)
                    current_state <= m_avalon_output.lock ? READY_LR : READY;
            end
            REQUESTING_AMO_R : begin //Read for an AMO
                if (INCLUDE_AMO) begin
                    ls_output.data_out <= m_avalon_input.readdata;
                    ls_output.data_valid <= ~m_avalon_input.waitrequest;
                    m_avalon_output.read <= m_avalon_input.waitrequest;
                    amo_unit_output.rmw_valid <= ~m_avalon_input.waitrequest;
                    if (~m_avalon_input.waitrequest)
                        current_state <= REQUESTING_AMO_M;
                end
            end
            REQUESTING_AMO_M : begin //One cycle for computing the AMO write value
                if (INCLUDE_AMO) begin
                    ls_output.data_valid <= 0;
                    m_avalon_output.writedata <= amo_unit_input.rd;
                    m_avalon_output.write <= 1;
                    amo_unit_output.rmw_valid <= 0;
                    current_state <= REQUESTING_AMO_W;
                end
            end
            REQUESTING_AMO_W : begin //Write for an AMO
                if (INCLUDE_AMO) begin
                    ls_output.ready <= ~m_avalon_input.waitrequest;
                    m_avalon_output.write <= m_avalon_input.waitrequest;
                    m_avalon_output.lock <= m_avalon_input.waitrequest;
                    write_outstanding <= m_avalon_input.waitrequest;
                    if (~m_avalon_input.waitrequest)
                        current_state <= READY;
                end
            end
            READY_LR : begin //Lock is held; hold for LR_WAIT cycles
                if (INCLUDE_AMO) begin
                    ls_output.ready <= ~ls_input.new_request | (request_is_sc & ~amo_unit_input.reservation_valid);
                    ls_output.data_out <= {31'b0, ~amo_unit_input.reservation_valid};
                    ls_output.data_valid <= ls_input.new_request & request_is_sc;
                    m_avalon_output.addr[31:2] <= ls_input.addr[31:2];
                    m_avalon_output.byteenable <= ls_input.be;
                    m_avalon_output.writedata <= ls_input.data_in;
                    m_avalon_output.read <= ls_input.new_request & ls_input.re & ~request_is_sc;
                    m_avalon_output.write <= ls_input.new_request & (ls_input.we | (request_is_sc & amo_unit_input.reservation_valid));
                    
                    write_outstanding <= ls_input.new_request & (ls_input.we | amo);
                    amo_unit_output.rmw_valid <= 0;
                    amo_unit_output.op <= amo_type;

                    if (ls_input.new_request)
                        m_avalon_output.lock <= amo;
                    else if (32'(lock_counter) == LR_WAIT-1)
                        m_avalon_output.lock <= 0;

                    lock_counter <= lock_counter + 1;

                    if (ls_input.new_request & (~amo | amo_type == AMO_LR_FN5))
                        current_state <= REQUESTING;
                    else if (ls_input.new_request & amo & amo_type != AMO_SC_FN5)
                        current_state <= REQUESTING_AMO_R;
                    else if (ls_input.new_request & amo & amo_type == AMO_SC_FN5 & amo_unit_input.reservation_valid)
                        current_state <= REQUESTING_SC;
                    else if (32'(lock_counter) == LR_WAIT-1 | ls_input.new_request)
                        current_state <= READY;
                end
            end
            REQUESTING_SC : begin //Exclusive write
                if (INCLUDE_AMO) begin
                    ls_output.ready <= ~m_avalon_input.waitrequest;
                    ls_output.data_valid <= 0;
                    m_avalon_output.write <= m_avalon_input.waitrequest;
                    m_avalon_output.lock <= m_avalon_input.waitrequest;
                    write_outstanding <= m_avalon_input.waitrequest;
                    if (~m_avalon_input.waitrequest)
                        current_state <= REQUESTING;
                end
            end
        endcase
        if (rst)
            current_state <= READY;
    end

endmodule
