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

module wishbone_master

    import riscv_types::*;

    #(
        parameter int unsigned LR_WAIT = 32, //The number of cycles the master holds cyc after an LR
        parameter logic INCLUDE_AMO = 1 //Required because the tools cannot fully optimize even if amo signals are tied off
    )
    (
        input logic clk,
        input logic rst,

        output logic write_outstanding,
        //wishbone_interface.master wishbone,
        master_wishbone_interface_output wishbone_output,
        master_wishbone_interface_input wishbone_input,
        
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

    logic[$clog2(LR_WAIT)-1:0] cyc_counter;
    logic request_is_sc;
    assign request_is_sc = amo & amo_type == AMO_SC_FN5;

    assign amo_unit_output.set_reservation = ls_input.new_request & amo & amo_type == AMO_LR_FN5;
    assign amo_unit_output.clear_reservation = ls_input.new_request;
    assign amo_unit_output.reservation = ls_input.addr;
    assign amo_unit_output.rs1 = ls_input.data_out;
    assign amo_unit_output.rs2 = wishbone_input.dat_w;

    assign wishbone_output.cti = '0;
    assign wishbone_output.bte = '0;

    always_ff @(posedge clk) begin
        wishbone_output.adr[1:0] <= '0;
        unique case (current_state)
            READY : begin //Accept any request
                ls_output.ready <= ~ls_input.new_request | request_is_sc;
                ls_output.data_out <= 32'b1;
                ls_output.data_valid <= ls_input.new_request & request_is_sc;
                wishbone_output.adr[31:2] <= ls_input.addr[31:2];
                wishbone_output.sel <= ls_input.we ? ls_input.be : '1;
                wishbone_output.dat_w <= ls_input.data_in;
                wishbone_output.we <= ls_input.we;
                wishbone_output.stb <= ls_input.new_request & ~request_is_sc;
                wishbone_output.cyc <= ls_input.new_request & ~request_is_sc;
                write_outstanding <= ls_input.new_request & (ls.we | amo);
                amo_unit_output.rmw_valid <= 0;
                amo_unit_output.op <= amo_type;
                cyc_counter <= amo ? 1 : 0;
                if (ls_input.new_request & (~amo | amo_type == AMO_LR_FN5))
                    current_state <= REQUESTING;
                else if (ls_input.new_request & amo & amo_type != AMO_SC_FN5)
                    current_state <= REQUESTING_AMO_R;
            end
            REQUESTING : begin //Wait for response
                ls_output.ready <= wishbone_input.ack;
                ls_output.data_out <= wishbone_input.dat_r;
                ls_output.data_valid <= ~wishbone_input.we & wishbone_input.ack;
                wishbone_output.stb <= ~wishbone_input.ack;
                wishbone_output.cyc <= ~wishbone_input.ack | cyc_counter[0];
                write_outstanding <= wishbone_input.we & ~wishbone_input.ack;
                if (wishbone_input.ack)
                    current_state <= cyc_counter[0] ? READY_LR : READY;
            end
            REQUESTING_AMO_R : begin //Read for an AMO
                if (INCLUDE_AMO) begin
                    ls_output.data_out <= wishbone_input.dat_r;
                    ls_output.data_valid <= wishbone_input.ack;
                    wishbone_output.stb <= ~wishbone_input.ack;
                    amo_unit_output.rmw_valid <= wishbone_input.ack;
                    if (wishbone_input.ack)
                        current_state <= REQUESTING_AMO_M;
                end
            end
            REQUESTING_AMO_M : begin //One cycle for computing the AMO write value
                if (INCLUDE_AMO) begin
                    ls_output.data_valid <= 0;
                    wishbone_output.dat_w <= amo_unit_input.rd;
                    wishbone_output.stb <= 1;
                    wishbone_output.we <= 1;
                    amo_unit_output.rmw_valid <= 0;
                    current_state <= REQUESTING_AMO_W;
                end
            end
            REQUESTING_AMO_W : begin //Write for an AMO
                if (INCLUDE_AMO) begin
                    ls_output.ready <= wishbone_input.ack;
                    wishbone_output.cyc <= ~wishbone_input.ack;
                    wishbone_output.stb <= ~wishbone_input.ack;
                    write_outstanding <= ~wishbone_input.ack;
                    if (wishbone_input.ack)
                        current_state <= READY;
                end
            end
            READY_LR : begin //Cyc is held; hold for LR_WAIT cycles
                if (INCLUDE_AMO) begin
                    ls_output.ready <= ~ls_input.new_request | (request_is_sc & ~amo_unit_input.reservation_valid);
                    ls_output.data_out <= {31'b0, ~amo_unit_input.reservation_valid};
                    ls_output.data_valid <= ls_input.new_request & request_is_sc;
                    wishbone_output.adr[31:2] <= ls_input.addr[31:2];
                    wishbone_output.sel <= ls_input.we ? ls.be : '1;
                    wishbone_output.dat_w <= ls_input.data_in;
                    wishbone_output.we <= ls_input.we | request_is_sc;
                    wishbone_output.stb <= ls_input.new_request & ~(request_is_sc & ~amo_unit.reservation_valid);
                    write_outstanding <= ls_input.new_request & (ls.we | amo);
                    amo_unit_output.rmw_valid <= 0;
                    amo_unit_output.op <= amo_type;

                    if (ls.new_request)
                        wishbone_output.cyc <= ~(request_is_sc & ~amo_unit_input.reservation_valid);
                    else if (32'(cyc_counter) == LR_WAIT-1)
                        wishbone_output.cyc <= 0;

                    cyc_counter <= cyc_counter + 1;

                    if (ls.new_request & (~amo | amo_type == AMO_LR_FN5))
                        current_state <= REQUESTING;
                    else if (ls_input.new_request & amo & amo_type != AMO_SC_FN5)
                        current_state <= REQUESTING_AMO_R;
                    else if (ls_input.new_request & amo & amo_type == AMO_SC_FN5 & amo_unit_input.reservation_valid)
                        current_state <= REQUESTING_SC;
                    else if (32'(cyc_counter) == LR_WAIT-1 | ls_input.new_request)
                        current_state <= READY;
                end
            end
            REQUESTING_SC : begin //Exclusive write
                if (INCLUDE_AMO) begin
                    ls_output.ready <= wishbone_input.ack;
                    ls_output.data_valid <= 0;
                    wishbone_output.stb = ~wishbone_input.ack;
                    wishbone_output.cyc = ~wishbone_input.ack;
                    write_outstanding <= ~wishbone_input.ack;
                    if (wishbone_input.ack)
                        current_state <= REQUESTING;
                end
            end
        endcase
        if (rst)
            current_state <= READY;
    end

endmodule
