/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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
    import riscv_types::*;
    import cva5_types::*;
    
module fetch

    

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter type DATA_TYPE = fetch_attributes_t
    )

    (
        input logic clk,
        input logic rst,

        input logic branch_flush,
        input gc_outputs_t gc,

        //ID Support
        input id_t pc_id,
        input logic pc_id_available,
        output logic pc_id_assigned,
        output logic fetch_complete,
        output fetch_metadata_t fetch_metadata,

        //branch_predictor_interface.fetch bp,
        fetch_branch_predictor_input bp_input,
        fetch_branch_predictor_output bp_output,
        
        //ras_interface.fetch ras,
        fetch_ras_interface_input ras_input,
        fetch_ras_interface_output ras_output,

        //Instruction Metadata
        output logic early_branch_flush,
        output logic early_branch_flush_ras_adjust,
        output logic [31:0] if_pc,
        output logic [31:0] fetch_instruction,

        //tlb_interface.requester tlb,
        requester_tlb_interface_output tlb_output,
        requester_tlb_interface_input tlb_input,
        
        //local_memory_interface.master instruction_bram,
        master_local_memory_interface_input instruction_bram_input,
        master_local_memory_interface_input instruction_bram_output,
        
        //wishbone_interface.master iwishbone,
        master_wishbone_interface_output iwishbone_output,
        master_wishbone_interface_output iwishbone_input,
        
        input logic icache_on,
        //mem_interface.ro_master mem
        master_mem_mem_interface_input mem_input,
        master_mem_mem_interface_output mem_output
    );

    localparam NUM_SUB_UNITS = int'(CONFIG.INCLUDE_ILOCAL_MEM) + int'(CONFIG.INCLUDE_ICACHE) + int'(CONFIG.INCLUDE_IBUS);
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS);

    localparam LOCAL_MEM_ID = 0;
    localparam ICACHE_ID = int'(CONFIG.INCLUDE_ILOCAL_MEM);
    localparam BUS_ID = ICACHE_ID + int'(CONFIG.INCLUDE_ICACHE);

    localparam MAX_OUTSTANDING_REQUESTS = 2;
    localparam MAX_OUTSTANDING_REQUESTS_W = $clog2(MAX_OUTSTANDING_REQUESTS);
    
    //Subunit signals
    //addr_utils_interface #(CONFIG.ILOCAL_MEM_ADDR.L, CONFIG.ILOCAL_MEM_ADDR.H) ilocal_mem_addr_utils ();
    //addr_utils_interface #(CONFIG.ICACHE_ADDR.L, CONFIG.ICACHE_ADDR.H) icache_addr_utils ();
    //addr_utils_interface #(CONFIG.IBUS_ADDR.L, CONFIG.IBUS_ADDR.H) ibus_addr_utils ();
    import addr_utils_pkg::*;

    addr_range_t ilocal_mem_addr_utils = '{
        base_addr: CONFIG.ILOCAL_MEM_ADDR.L,
        upper_bound: CONFIG.ILOCAL_MEM_ADDR.H
    };
    
    addr_range_t icache_addr_utils = '{
        base_addr: CONFIG.ICACHE_ADDR.L,
        upper_bound: CONFIG.ICACHE_ADDR.H
    };
    
    addr_range_t ibus_addr_utils = '{
        base_addr: CONFIG.IBUS_ADDR.L,
        upper_bound: CONFIG.IBUS_ADDR.H
    };

    

    //memory_sub_unit_interface sub_unit[NUM_SUB_UNITS-1:0]();
    controller_memory_sub_unit_interface_input sub_unit_controller_input[NUM_SUB_UNITS-1:0];
    controller_memory_sub_unit_interface_output sub_unit_controller_output[NUM_SUB_UNITS-1:0];
    responder_memory_sub_unit_interface_input sub_unit_responder_input[NUM_SUB_UNITS-1:0];
    responder_memory_sub_unit_interface_output sub_unit_responder_output[NUM_SUB_UNITS-1:0];

    //amo_interface unused();
    subunit_amo_interface_input unused_subunit_input;
    subunit_amo_interface_output unused_subunit_output;
    amo_unit_amo_interface_input unused_amo_unit_input;
    amo_unit_amo_interface_output unused_amo_unit_output;
    
    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];

    logic units_ready;
    logic address_valid;

    /*typedef struct packed{
        logic is_predicted_branch_or_jump;
        logic is_branch;
        logic [31:0] early_flush_pc;
        logic address_valid;
        logic mmu_fault;
        logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    } fetch_attributes_t;*/
    fetch_attributes_t fetch_attr;

    logic [MAX_OUTSTANDING_REQUESTS_W:0] inflight_count;
    logic [MAX_OUTSTANDING_REQUESTS_W:0] inflight_count_next;
    logic [MAX_OUTSTANDING_REQUESTS_W:0] flush_count;
    logic [MAX_OUTSTANDING_REQUESTS_W:0] flush_count_next;


    logic [31:0] pc_plus_4;
    logic [31:0] early_flush_pc;
    logic [31:0] pc_mux [5];
    logic [2:0] pc_sel;
    logic [31:0] next_pc;
    logic [31:0] pc;

    logic flush_or_rst;
    //fifo_interface #(.DATA_TYPE(fetch_attributes_t)) fetch_attr_fifo();

    enqueue_fifo_interface_input fetch_attr_fifo_enqueue_input;
    enqueue_fifo_interface_output_fetch_attributes fetch_attr_fifo_enqueue_output;
    dequeue_fifo_interface_input_fetch_attributes fetch_attr_fifo_dequeue_input;
    dequeue_fifo_interface_output fetch_attr_fifo_dequeue_output;
    structure_fifo_interface_input_fetch_attributes fetch_attr_fifo_structure_input;
    structure_fifo_interface_output_fetch_attributes fetch_attr_fifo_structure_output;

    logic update_pc;
    logic new_mem_request;
    logic exception_pending;
    logic internal_fetch_complete;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////
    //Fetch PC
    assign update_pc = new_mem_request | gc.fetch_flush | early_branch_flush;
    always_ff @(posedge clk) begin
        if (gc.init_clear)
            pc <= CONFIG.CSRS.RESET_VEC;
        else if (update_pc)
            pc <= {next_pc[31:2], 2'b0};
    end

    assign pc_plus_4 = pc + 4;

    priority_encoder #(.WIDTH(5))
    pc_sel_encoder (
        .priority_vector ({1'b1, bp_input.use_prediction, early_branch_flush, branch_flush, gc.pc_override}),
        .encoded_result (pc_sel)
    );
    assign pc_mux[0] = gc.pc;
    assign pc_mux[1] = bp_input.branch_flush_pc;
    assign pc_mux[2] = early_flush_pc;
    assign pc_mux[3] = bp_input.is_return ? ras_input.addr : bp_input.predicted_pc;
    assign pc_mux[4] = pc_plus_4;
    assign next_pc = pc_mux[pc_sel];

    //If an exception occurs here in the fetch logic,
    //hold the fetching of data from memory until the status of the
    //exception has been resolved
    always_ff @(posedge clk) begin
        if (flush_or_rst)
            exception_pending <= 0;
        else if ((tlb_input.is_fault & ~fetch_attr_fifo_enqueue_input.full) | (new_mem_request & ~address_valid))
            exception_pending <= 1;
    end

    assign bp_output.new_mem_request = update_pc;
    assign bp_output.next_pc = next_pc;
    assign bp_output.if_pc = pc;
    assign bp_output.pc_id = pc_id;
    assign bp_output.pc_id_assigned = pc_id_assigned;

    ////////////////////////////////////////////////////
    //RAS support
    logic ras_update_permitted;
    assign ras_update_permitted = bp_input.use_prediction & new_mem_request & ~(branch_flush | gc.pc_override | early_branch_flush);

    assign ras_output.pop = bp_input.is_return & ras_update_permitted;
    assign ras_output.push = bp_input.is_call & ras_update_permitted;
    assign ras_output.branch_fetched = bp_input.is_branch & ras_update_permitted;
    assign ras_output.new_addr = pc_plus_4;

    ////////////////////////////////////////////////////
    //TLB
    assign tlb_output.virtual_address = pc;
    assign tlb_output.rnw = 1;
    assign tlb_output.new_request = tlb_input.ready & pc_id_available & ~fetch_attr_fifo_enqueue_input.full & (~exception_pending) & (~gc.fetch_hold);

    //////////////////////////////////////////////
    //Issue Control Signals
    assign flush_or_rst = (rst | gc.fetch_flush | early_branch_flush);

    assign new_mem_request = tlb_input.done & units_ready & ~gc.fetch_hold & ~fetch_attr_fifo_enqueue_input.full;
    assign pc_id_assigned = new_mem_request | (tlb_input.is_fault & ~fetch_attr_fifo_enqueue_input.full);

    //////////////////////////////////////////////
    //Subunit Tracking
    logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    one_hot_to_integer #(NUM_SUB_UNITS)
    hit_way_conv (
        .one_hot (sub_unit_address_match), 
        .int_out (subunit_id)
    );
    /*assign fetch_attr_fifo_enqueue_output.data_in = '{
        is_predicted_branch_or_jump : bp_input.use_prediction,
        is_branch : (bp_input.use_prediction & bp_input.is_branch),
        early_flush_pc : pc_plus_4,
        address_valid : address_valid,
        mmu_fault : tlb_input.is_fault,
        subunit_id : subunit_id
    };*/
    
    assign fetch_attr_fifo_enqueue_output.data_in.is_predicted_branch_or_jump = bp_input.use_prediction;
assign fetch_attr_fifo_enqueue_output.data_in.is_branch = bp_input.use_prediction & bp_input.is_branch;
assign fetch_attr_fifo_enqueue_output.data_in.early_flush_pc = pc_plus_4;
assign fetch_attr_fifo_enqueue_output.data_in.address_valid = address_valid;
assign fetch_attr_fifo_enqueue_output.data_in.mmu_fault = tlb_input.is_fault;
assign fetch_attr_fifo_enqueue_output.data_in.subunit_id = subunit_id;
    assign fetch_attr_fifo_enqueue_output.push = pc_id_assigned;
    assign fetch_attr_fifo_enqueue_output.potential_push = pc_id_assigned;
    assign fetch_attr_fifo_dequeue_output.pop = internal_fetch_complete;

    cva5_fifo #(.DATA_TYPE(fetch_attributes_t), .FIFO_DEPTH(MAX_OUTSTANDING_REQUESTS))
    attributes_fifo (
        .clk (clk), 
        .rst (rst), 
        .fifo_input_fetch_attributes (fetch_attr_fifo_structure_input),
        .fifo_output_fetch_attributes (fetch_attr_fifo_structure_output)
    );
    assign fetch_attr = fetch_attr_fifo_dequeue_input.data_out;
    assign early_flush_pc = fetch_attr.early_flush_pc;

    assign inflight_count_next = inflight_count + MAX_OUTSTANDING_REQUESTS_W'(fetch_attr_fifo_enqueue_input.push) - MAX_OUTSTANDING_REQUESTS_W'(fetch_attr_fifo_structure_input.pop);
    always_ff @(posedge clk) begin
        if (rst)
            inflight_count <= 0;
        else
            inflight_count <= inflight_count_next;
    end

    always_ff @(posedge clk) begin
        if (rst)
            flush_count <= 0;
        else if (gc.fetch_flush | early_branch_flush)
            flush_count <= inflight_count_next;
        else if (|flush_count & fetch_attr_fifo_structure_input.pop)
            flush_count <= flush_count - 1;
    end

    ////////////////////////////////////////////////////
    //Subunit Interfaces
    //In the case of a gc.fetch_flush, a request may already be in progress
    //for any sub unit.  That request can either be completed or aborted.
    //In either case, data_valid must NOT be asserted.
    generate for (i=0; i < NUM_SUB_UNITS; i++) begin : gen_fetch_sources
        assign sub_unit_responder_output[i].new_request = fetch_attr_fifo_structure_input.push & sub_unit_address_match[i] & ~tlb_input.is_fault;
        assign sub_unit_responder_output[i].addr = tlb_input.physical_address;
        assign sub_unit_responder_output[i].re = 1;
        assign sub_unit_responder_output[i].we = 0;
        assign sub_unit_responder_output[i].be = '0;
        assign sub_unit_responder_output[i].data_in = '0;
        

        assign unit_ready[i] = sub_unit_responder_input[i].ready;
        assign unit_data_valid[i] = sub_unit_responder_input[i].data_valid;
        assign unit_data_array[i] = sub_unit_responder_input[i].data_out;
    end
    endgenerate

    generate if (CONFIG.INCLUDE_ILOCAL_MEM) begin : gen_fetch_local_mem
        assign sub_unit_address_match[LOCAL_MEM_ID] = ilocal_mem_addr_utils.address_range_check(tlb_input.physical_address);
        local_mem_sub_unit i_local_mem (
            .clk (clk), 
            .rst (rst),
            .write_outstanding (),
            .amo (1'b0),
            .amo_type ('x),
            .amo_unit_input (unused_subunit_input),
            .amo_unit_output (unused_subunit_output),
            .unit_input (sub_unit_responder_input[LOCAL_MEM_ID]),
            .unit_output (sub_unit_responder_output[LOCAL_MEM_ID]),
            .local_mem_input (instruction_bram_input),
            .local_mem_output (instruction_bram_output)
        );
    end
    endgenerate

    generate if (CONFIG.INCLUDE_IBUS) begin : gen_fetch_ibus
        assign sub_unit_address_match[BUS_ID] = ibus_addr_utils.address_range_check(tlb_input.physical_address);
        wishbone_master iwishbone_bus (
            .clk (clk),
            .rst (rst),
            .write_outstanding (),
            .amo (1'b0),
            .amo_type ('x),
            .amo_unit_input (unused_subunit_input),
            .amo_unit_output (unused_subunit_output),
            .wishbone_input (iwishbone_input),
            .wishbone_output (iwishbone_output),
            .ls_input (sub_unit_responder_input[BUS_ID]),
            .ls_output (sub_unit_responder_output[BUS_ID])
        );
    end
    endgenerate

    generate if (CONFIG.INCLUDE_ICACHE) begin : gen_fetch_icache
        ////////////////////////////////////////////////////
        //Instruction fence
        //A fence first prevents any new instructions from being issued then waits for inflight fetches to complete
        //The fence signal can only be delivered to the icache once it is idle
        //This logic will be optimized away when instruction fences aren't enabled as gc.fetch_ifence will be constant 0
        logic ifence_pending;
        logic ifence_start;
        assign ifence_start = ifence_pending & ~|inflight_count_next;
        
        always_ff @(posedge clk) begin
            if (rst)
                ifence_pending <= 0;
            else begin
                if (gc.fetch_ifence)
                    ifence_pending <= 1;
                else if (~|inflight_count_next)
                    ifence_pending <= 0;
            end
        end

        assign sub_unit_address_match[ICACHE_ID] = icache_addr_utils.address_range_check(tlb_input.physical_address);
        icache #(.CONFIG(CONFIG))
        i_cache (
            .clk (clk), 
            .rst (rst),
            .ifence (ifence_start),
            .icache_on (icache_on),
            .mem_input (mem_input),
            .mem_output (mem_output),
            .fetch_sub_input (sub_unit_responder_input[ICACHE_ID]),
            .fetch_sub_output (sub_unit_responder_output[ICACHE_ID])
        );
    end endgenerate

    assign units_ready = &unit_ready;
    assign address_valid = |sub_unit_address_match;

    ////////////////////////////////////////////////////
    //Instruction metada updates
    logic valid_fetch_result;
    assign valid_fetch_result = CONFIG.MODES != BARE ? (fetch_attr_fifo_dequeue_input.valid & fetch_attr.address_valid & (~fetch_attr.mmu_fault)) : 1;

    assign if_pc = pc;
    assign fetch_metadata.ok = valid_fetch_result;
    assign fetch_metadata.error_code = fetch_attr.mmu_fault ? INST_PAGE_FAULT : INST_ACCESS_FAULT;

    assign fetch_instruction = unit_data_array[fetch_attr.subunit_id];

    assign internal_fetch_complete = fetch_attr_fifo_dequeue_input.valid & (~valid_fetch_result | |unit_data_valid);//allow instruction to propagate to decode if address is invalid
    assign fetch_complete = internal_fetch_complete & ~|flush_count;

    ////////////////////////////////////////////////////
    //Branch Predictor corruption check
    //Needed if instruction memory is changed after any branches have been executed
    generate if (CONFIG.INCLUDE_IFENCE | CONFIG.MODES == MSU) begin : gen_branch_corruption_check
        logic is_branch_or_jump;
        assign is_branch_or_jump = fetch_instruction[6:2] inside {JAL_T, JALR_T, BRANCH_T};
        assign early_branch_flush = (valid_fetch_result & (|unit_data_valid)) & fetch_attr.is_predicted_branch_or_jump & (~is_branch_or_jump) & (~|flush_count);
        assign early_branch_flush_ras_adjust = (valid_fetch_result & (|unit_data_valid)) & fetch_attr.is_branch & (~is_branch_or_jump) & (~|flush_count);
    end endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    spurious_fetch_complete_assertion:
    assert property (@(posedge clk) disable iff (rst) (|unit_data_valid) |-> (fetch_attr_fifo_dequeue_input.valid && unit_data_valid[fetch_attr.subunit_id]))
        else $error("Spurious fetch complete detected!");

endmodule
