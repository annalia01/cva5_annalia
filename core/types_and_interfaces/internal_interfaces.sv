/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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
import cva5_types::*;
import csr_types::*;
import riscv_types::*;

parameter type DATA_TYPE = logic;

typedef struct {
    logic [31:0] if_pc;
    id_t         if_id;
    logic        new_mem_request;
    logic [31:0] next_pc;
    id_t         pc_id;
    logic        pc_id_assigned;
} branch_predictor_branch_predictor_input;

typedef struct {
    logic [31:0] branch_flush_pc;
    logic [31:0] predicted_pc;
    logic        use_prediction;
    logic        is_return;
    logic        is_call;
    logic        is_branch;
} branch_predictor_branch_predictor_output;

typedef struct {
    logic [31:0] branch_flush_pc;
    logic [31:0] predicted_pc;
    logic        use_prediction;
    logic        is_return;
    logic        is_call;
    logic        is_branch;
} fetch_branch_predictor_input;

typedef struct packed {
    logic [31:0] if_pc;
    id_t         if_id;
    logic        new_mem_request;
    logic [31:0] next_pc;
    id_t         pc_id;
    logic        pc_id_assigned;
} fetch_branch_predictor_output;

typedef struct {
    logic        ready;
} decode_unit_issue_interface_input;

typedef struct {
    logic        possible_issue;
    logic        new_request;
    id_t         id;
} decode_unit_issue_interface_output;

typedef struct {
    logic        possible_issue;
    logic        new_request;
    id_t         id;
} unit_unit_issue_interface_input;

typedef struct {
    logic        ready;
} unit_unit_issue_interface_output;

parameter DATA_WIDTH = 32;
parameter NUM_WB_GROUPS = 3;
parameter READ_PORTS = 2;
typedef struct {
    logic ack;
} unit_unit_writeback_interface_input;

typedef struct {
    logic done;
    id_t id;
    logic [DATA_WIDTH-1:0] rd;
} unit_unit_writeback_interface_output;

typedef struct {
    logic done;
    id_t id;
    logic [DATA_WIDTH-1:0] rd;
} wb_unit_writeback_interface_input;

typedef struct {
    logic ack;
} wb_unit_writeback_interface_output;

typedef struct {
    logic branch_retired;
} branch_predictor_ras_interface_output;

typedef struct {
    logic push;
    logic pop;
    logic [31:0] new_addr;
    logic branch_fetched;
    logic branch_retired;
} self_ras_interface_input;

typedef struct {
    logic [31:0] addr;
} self_ras_interface_output;

typedef struct {
    logic [31:0] addr;
} fetch_ras_interface_input;

typedef struct {
    logic pop;
    logic push;
    logic [31:0] new_addr;
    logic branch_fetched;
} fetch_ras_interface_output;

typedef struct {
    logic valid;
    logic possible;
    exception_code_t code;
    logic [31:0] tval;
    logic [31:0] pc;
    logic discard;
} unit_exception_output;

typedef struct {
    logic valid;
    logic possible;
    exception_code_t code;
    logic [31:0] tval;
    logic [31:0] pc;
    logic discard;
} econtrol_exception_interface_input;


package fifo_structs_pkg;

  parameter type DATA_TYPE = logic; // default generico, sovrascrivibile

  typedef struct {
      logic full;
  } enqueue_fifo_interface_input;

  typedef struct {
      DATA_TYPE data_in;
      logic push;
      logic potential_push;
  } enqueue_fifo_interface_output;

  typedef struct {
      logic valid;
      DATA_TYPE data_out;
  } dequeue_fifo_interface_input;

  typedef struct {
      logic pop;
  } dequeue_fifo_interface_output;

  typedef struct {
      logic push;
      logic pop;
      DATA_TYPE data_in;
      logic potential_push;
  } structure_fifo_interface_input;

  typedef struct {
      DATA_TYPE data_out;
      logic valid;
      logic full;
  } structure_fifo_interface_output;

endpackage

typedef struct {
    logic [31:0] virtual_address;
    logic request;
    logic execute;
    logic rnw;
    logic [21:0] satp_ppn;
    logic mxr;
    logic sum;
    privilege_t privilege;
} mmu_mmu_interface_input;

typedef struct {
    logic write_entry;
    logic superpage;
    pte_perms_t perms;
    logic [19:0] upper_physical_address;
    logic is_fault;
} mmu_mmu_interface_output;

typedef struct {
    logic write_entry;
    logic superpage;
    pte_perms_t perms;
    logic [19:0] upper_physical_address;
    logic is_fault;
    logic mxr;
    logic sum;
    privilege_t privilege;
} tlb_mmu_interface_input;

typedef struct {
    logic request;
    logic [31:0] virtual_address;
    logic execute;
    logic rnw;
} tlb_mmu_interface_output;

typedef struct {
    logic [21:0] satp_ppn;
    logic mxr;
    logic sum;
    privilege_t privilege;
} csr_mmu_interface_output;

typedef struct {
    logic new_request;
    logic [31:0] virtual_address;
    logic rnw;
} tlb_tlb_interface_input;

typedef struct {
    logic ready;
    logic done;
    logic is_fault;
    logic [31:0] physical_address;
} tlb_tlb_interface_output;

typedef struct {
    logic new_request;
    logic [31:0] virtual_address;
    logic rnw;
} requester_tlb_interface_output;

typedef struct {
    logic ready;
    logic done;
    logic is_fault;
    logic [31:0] physical_address;
} requester_tlb_interface_input;

typedef struct {
    lsq_entry_t data_in;
    logic potential_push;
    logic push;
    logic load_pop;
    logic store_pop;
    logic addr_push;
    lsq_addr_entry_t addr_data_in;
} ls_load_store_queue_interface_output;

typedef struct {
    logic full;
    data_access_shared_inputs_t load_data_out;
    data_access_shared_inputs_t store_data_out;
    logic load_valid;
    logic store_valid;
    logic sq_empty;
    logic empty;
} ls_load_store_queue_interface_input;

typedef struct {
    lsq_entry_t data_in;
    logic potential_push;
    logic push;
    logic load_pop;
    logic store_pop;
    logic addr_push;
    lsq_addr_entry_t addr_data_in;
} queue_load_store_queue_interface_input;

typedef struct {
    logic full;
    data_access_shared_inputs_t load_data_out;
    data_access_shared_inputs_t store_data_out;
    logic load_valid;
    logic store_valid;
    logic sq_empty;
    logic empty;
} queue_load_store_queue_interface_output;

typedef struct {
    lsq_entry_t data_in;
    logic push;
    logic pop;
} ls_store_queue_interface_output;

typedef struct {
    logic full;
    sq_entry_t data_out;
    logic valid;
    logic empty;
} ls_store_queue_interface_input;

typedef struct {
    lsq_entry_t data_in;
    logic push;
    logic pop;
} queue_store_queue_interface_input;

typedef struct {
    logic full;
    sq_entry_t data_out;
    logic valid;
    logic empty;
} queue_store_queue_interface_output;

package cache_functions_pkg;

    parameter int TAG_W = 8;
    parameter int LINE_W = 4;
    parameter int SUB_LINE_W = 2;

    function logic [LINE_W-1:0] xor_mask (int WAY);
        logic [LINE_W-1:0] mask;
        for (int i = 0; i < LINE_W; i++)
            mask[i] = ((WAY % 2) == 0) ? 1'b1 : 1'b0;
        return mask;
    endfunction

    function logic [LINE_W-1:0] getHashedLineAddr (logic[31:0] addr, int WAY);
        return addr[2 + SUB_LINE_W +: LINE_W] ^ 
               (addr[2 + SUB_LINE_W + LINE_W +: LINE_W] & xor_mask(WAY));
    endfunction

    function logic [TAG_W-1:0] getTag(logic[31:0] addr);
        return addr[2 + LINE_W + SUB_LINE_W +: TAG_W];
    endfunction

    function logic [LINE_W-1:0] getTagLineAddr (logic[31:0] addr);
        return addr[2 + SUB_LINE_W +: LINE_W];
    endfunction

    function logic [LINE_W + SUB_LINE_W - 1:0] getDataLineAddr (logic[31:0] addr);
        return addr[2 +: LINE_W + SUB_LINE_W];
    endfunction

endpackage

package addr_utils_pkg;

    typedef struct {
        logic [31:0] base_addr;
        logic [31:0] upper_bound;
    } addr_range_t;

    function logic address_range_check(
        input logic [31:0] addr,
        input addr_range_t range
    );
        /* verilator lint_off UNSIGNED */
        /* verilator lint_off CMPCONST */
        return (addr >= range.base_addr) && (addr <= range.upper_bound);
        /* verilator lint_on UNSIGNED */
        /* verilator lint_on CMPCONST */
    endfunction

endpackage


typedef struct {
    logic new_request;
    logic [31:0] addr;
    logic re;
    logic we;
    logic [3:0] be;
    logic [31:0] data_in;
} controller_memory_sub_unit_interface_output;

typedef struct {
    logic [31:0] data_out;
    logic data_valid;
    logic ready;
} controller_memory_sub_unit_interface_input;

typedef struct packed {
    logic [31:0] data_out;
    logic data_valid;
    logic ready;
} responder_memory_sub_unit_interface_output;

typedef struct {
    logic new_request;
    logic [31:0] addr;
    logic re;
    logic we;
    logic [3:0] be;
    logic [31:0] data_in;
} responder_memory_sub_unit_interface_input;

// unsigned_division_interface
typedef struct {
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] quotient;
    logic done;
} unsigned_division_interface_requester_input;

typedef struct {
    logic [DATA_WIDTH-1:0] dividend;
    logic [$clog2(DATA_WIDTH)-1:0] dividend_CLZ;
    logic [DATA_WIDTH-1:0] divisor;
    logic [$clog2(DATA_WIDTH)-1:0] divisor_CLZ;
    logic divisor_is_zero;
    logic start;
} unsigned_division_interface_requester_output;

typedef struct {
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] quotient;
    logic done;
} unsigned_division_interface_divider_output;

typedef struct {
    logic [DATA_WIDTH-1:0] dividend;
    logic [$clog2(DATA_WIDTH)-1:0] dividend_CLZ;
    logic [DATA_WIDTH-1:0] divisor;
    logic [$clog2(DATA_WIDTH)-1:0] divisor_CLZ;
    logic divisor_is_zero;
    logic start;
} unsigned_division_interface_divider_input;

typedef struct {
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] result;
    logic done;
} unsigned_sqrt_interface_requester_input;

typedef struct {
    logic [DATA_WIDTH-1:0] radicand;
    logic start;
} unsigned_sqrt_interface_requester_output;

typedef struct {
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] result;
    logic done;
} unsigned_sqrt_interface_sqrt_output;

typedef struct {
    logic [DATA_WIDTH-1:0] radicand;
    logic start;
} unsigned_sqrt_interface_sqrt_input;

typedef struct {
    rs_addr_t rd_addr;
    rs_addr_t rs_addr [READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rd_wb_group;
    logic uses_rd;
    id_t id;
} renamer_renamer_interface_input;

typedef struct {
    phys_addr_t phys_rs_addr [READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [READ_PORTS];
    phys_addr_t phys_rd_addr;
} renamer_renamer_interface_output;

typedef struct {
    phys_addr_t phys_rs_addr [READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [READ_PORTS];
    phys_addr_t phys_rd_addr;
} decode_renamer_interface_input;

typedef struct {
    rs_addr_t rd_addr;
    rs_addr_t rs_addr [READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rd_wb_group;
    logic uses_rd;
    id_t id;
} decode_renamer_interface_output;
 
typedef struct {
    phys_addr_t phys_rs_addr [READ_PORTS];
    phys_addr_t phys_rd_addr;
    logic single_cycle_or_flush;
    logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [READ_PORTS];
} register_file_register_file_issue_interface_input;

typedef struct {
    logic [DATA_WIDTH-1:0] data [READ_PORTS];
    logic inuse [READ_PORTS];
} register_file_register_file_issue_interface_output;

typedef struct {
    logic [DATA_WIDTH-1:0] data [READ_PORTS];
    logic inuse [READ_PORTS];
} issue_register_file_issue_interface_input;

typedef struct {
    phys_addr_t phys_rs_addr [2];
    phys_addr_t phys_rd_addr;
    logic single_cycle_or_flush;
    logic [$clog2(3)-1:0] rs_wb_group [2];
} issue_register_file_issue_interface_output;

typedef struct {
    logic ack;
} fp_intermediate_wb_interface_unit_input;

typedef struct {
    id_t id;
    logic done;
    fp_t rd;
    logic expo_overflow;
    fflags_t fflags;
    rm_t rm;
    logic carry;
    logic safe;
    logic hidden;
    grs_t grs;
    fp_shift_amt_t clz;
    logic right_shift;
    fp_shift_amt_t right_shift_amt;
    logic subnormal;
    logic ignore_max_expo;
    logic d2s;
} fp_intermediate_wb_interface_unit_output;

typedef struct {
    logic ack;
} fp_intermediate_wb_interface_wb_output;

typedef struct {
    id_t id;
    logic done;
    fp_t rd;
    logic expo_overflow;
    fflags_t fflags;
    rm_t rm;
    logic carry;
    logic safe;
    logic hidden;
    grs_t grs;
    fp_shift_amt_t clz;
    logic right_shift;
    fp_shift_amt_t right_shift_amt;
    logic subnormal;
    logic ignore_max_expo;
    logic d2s;
} fp_intermediate_wb_interface_wb_input;

typedef struct {
    logic reservation_valid;
    logic [31:0] rd;
} subunit_amo_interface_input;

typedef struct {
    logic set_reservation;
    logic clear_reservation;
    logic [31:0] reservation;
    logic rmw_valid;
    amo_t op;
    logic [31:0] rs1;
    logic [31:0] rs2;
} subunit_amo_interface_output;

typedef struct {
    logic set_reservation;
    logic clear_reservation;
    logic [31:0] reservation;
    logic rmw_valid;
    amo_t op;
    logic [31:0] rs1;
    logic [31:0] rs2;
} amo_unit_amo_interface_input;

typedef struct {
    logic reservation_valid;
    logic [31:0] rd;
} amo_unit_amo_interface_output;
