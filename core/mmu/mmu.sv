/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

module mmu

    import csr_types::*;

    (
        input logic clk,
        input logic rst,
        //mmu_interface.mmu mmu,
        mmu_mmu_interface_input mmu_input,
        mmu_mmu_interface_output mmu_output,
        
        input logic abort_request,
        //mem_interface.ro_master mem

        master_ro_mem_interface_input mem_input,
        master_ro_mem_interface_output mem_output
    );

    typedef struct packed{
        logic [11:0] ppn1;
        logic [9:0] ppn0;
        logic [1:0] reserved;
        pte_perms_t perms;
    } pte_t;

    typedef enum  {
        IDLE = 0,
        SEND_REQUEST_1 = 1,
        WAIT_REQUEST_1 = 2,
        SEND_REQUEST_2 = 3,
        WAIT_REQUEST_2 = 4,
        COMPLETE_SUCCESS = 5,
        COMPLETE_FAULT = 6
    } mmu_state_t;
    logic [6:0] state;
    logic [6:0] next_state;

    pte_t pte;
    logic perms_valid;

    localparam MAX_ABORTED_REQUESTS = 4;
    logic abort_queue_full;
    logic discard_data;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //L1 arbiter Interfrace
    assign mem_output.rlen = '0;

    assign mem_output.request = (state[SEND_REQUEST_1] | state[SEND_REQUEST_2]) & ~abort_request;

    //Page Table addresses
    always_ff @ (posedge clk) begin
        if (state[IDLE] | (mem.rvalid & ~discard_data)) begin
            if (state[IDLE])
                mem_output.addr <= {mmu_input.satp_ppn[19:0], mmu_input.virtual_address[31:22]};
            else
                mem_output.addr <= {pte.ppn1[9:0], pte.ppn0, mmu_input.virtual_address[21:12]};
        end
    end

    assign pte = mem_input.rdata;

    ////////////////////////////////////////////////////
    //Supports unlimited tracking of aborted requests
    //Assumption: memory requests are returned in-order
    localparam COUNT_W = $clog2(MAX_ABORTED_REQUESTS);
    logic [COUNT_W:0] abort_tracking;
    logic delayed_abort;
    logic delayed_abort_complete;

    assign delayed_abort = abort_request & (state[WAIT_REQUEST_1] | state[WAIT_REQUEST_2]);
    assign delayed_abort_complete = (discard_data | abort_request) & mem_input.rvalid;
    always_ff @ (posedge clk) begin
        if (rst)
            abort_tracking <= 0;
        else
            abort_tracking <= abort_tracking - COUNT_W'(delayed_abort) + COUNT_W'(delayed_abort_complete);
    end

    assign discard_data = abort_tracking[COUNT_W];
    assign abort_queue_full = abort_tracking[COUNT_W] & ~|abort_tracking[COUNT_W-1:0];

    perms_check perm (
        .pte_perms(pte.perms),
        .rnw(mmu_input.rnw),
        .execute(mmu_input.execute),
        .mxr(mmu_input.mxr),
        .sum(mmu_input.sum),
        .privilege(mmu_input.privilege),
        .valid(perms_valid)
    );

    ////////////////////////////////////////////////////
    //State Machine
    always_comb begin
        next_state = state;
        case (1'b1)
            state[IDLE] :
                if (mmu_input.request & ~abort_queue_full)
                    next_state = 2**SEND_REQUEST_1;
            state[SEND_REQUEST_1] : 
                if (mem_input.ack)
                    next_state = 2**WAIT_REQUEST_1;
            state[WAIT_REQUEST_1] :
                if (mem_input.rvalid & ~discard_data) begin
                    if (~pte.perms.v | (~pte.perms.r & pte.perms.w)) //page not valid OR invalid xwr pattern
                        next_state = 2**COMPLETE_FAULT;
                    else if (pte.perms.v & (pte.perms.r | pte.perms.x)) begin//superpage (all remaining xwr patterns other than all zeros)
                        if (perms_valid & ~|pte.ppn0) //check for misaligned superpage
                            next_state = 2**COMPLETE_SUCCESS;
                        else
                            next_state = 2**COMPLETE_FAULT;
                    end else //(pte.perms.v & ~pte.perms.x & ~pte.perms.w & ~pte.perms.r) pointer to next level in page table
                        next_state = 2**SEND_REQUEST_2;
                end
            state[SEND_REQUEST_2] : 
                if (mem_input.ack)
                    next_state = 2**WAIT_REQUEST_2;
            state[WAIT_REQUEST_2] : 
                if (mem_input.rvalid & ~discard_data) begin
                    if (~perms_valid | ~pte.perms.v | (~pte.perms.r & pte.perms.w)) //perm fail or invalid
                        next_state = 2**COMPLETE_FAULT;
                    else
                        next_state = 2**COMPLETE_SUCCESS;
                end
            state[COMPLETE_SUCCESS], state[COMPLETE_FAULT]  :
                next_state = 2**IDLE;
        endcase
        //If request is aborted, return to IDLE
        if (abort_request)
            next_state = 2**IDLE;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            state <= 2**IDLE;
        else
            state <= next_state;
    end

    ////////////////////////////////////////////////////
    //TLB return path
    always_ff @ (posedge clk) begin
        if (mem_input.rvalid) begin
            mmu_output.superpage <= state[WAIT_REQUEST_1];
            mmu_output.perms.d <= pte.perms.d;
            mmu_output.perms.a <= pte.perms.a;
            mmu_output.perms.g <= pte.perms.g | (state[WAIT_REQUEST_2] & mmu_input.perms.g);
            mmu_output.perms.u <= pte.perms.u;
            mmu_output.perms.x <= pte.perms.x;
            mmu_output.perms.w <= pte.perms.w;
            mmu_output.perms.r <= pte.perms.r;
            mmu_output.perms.v <= pte.perms.v;
            mmu_output.upper_physical_address[19:10] <= pte.ppn1[9:0];
            mmu_output.upper_physical_address[9:0] <= state[WAIT_REQUEST_2] ? pte.ppn0 : mmu_input.virtual_address[21:12];
        end
    end
    assign mmu_output.write_entry = state[COMPLETE_SUCCESS];
    assign mmu_output.is_fault = state[COMPLETE_FAULT];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    mmu_spurious_l1_response:
    assert property (@(posedge clk) disable iff (rst) (mem_input.rvalid) |-> (state[WAIT_REQUEST_1] | state[WAIT_REQUEST_2]))
        else $error("mmu recieved response without a request");

    //TLB request remains high until it recieves a response from the MMU unless
    //the transaction is aborted.  As such, if TLB request is low and we are not in the
    //IDLE state, then our current processor state has been corrupted
    mmu_tlb_state_mismatch:
        assert property (@(posedge clk) disable iff (rst) (mmu_input.request) |-> (state[IDLE]))
        else $error("MMU and TLB state mismatch");

endmodule
