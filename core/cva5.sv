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



module cva5

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import fpu_types::*;
    import csr_types::*;

    #(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        //local_memory_interface.master instruction_bram,
        master_local_memory_interface_input instruction_bram_input,
        master_local_memory_interface_output instruction_bram_output,
        
        //local_memory_interface.master data_bram,
        master_local_memory_interface_input data_bram_input,
        master_local_memory_interface_output data_bram_output,

        //axi_interface.master m_axi,
        master_axi_interface_output m_axi_output,
        master_axi_interface_input m_axi_input,
        
        //avalon_interface.master m_avalon,
        master_avalon_interface_input m_avalon_input,
        master_avalon_interface_output m_avalon_output,

        //wishbone_interface.master dwishbone,
        master_wishbone_interface_output dwishbone_output,
        master_wishbone_interface_input dwishbone_input,

        //wishbone_interface.master iwishbone,
        master_wishbone_interface_output iwishbone_output,
        master_wishbone_interface_input iwishbone_input,

        //mem_interface.mem_master mem,
        master_mem_mem_interface_input mem_input,
        master_mem_mem_interface_output mem_output,

        input logic [63:0] mtime,
        input interrupt_t s_interrupt,
        input interrupt_t m_interrupt
    );

    ////////////////////////////////////////////////////
    //Connecting Signals
    //mem_interface dcache_mem();
    master_ro_mem_interface_input dcache_mem_input_master_ro;
    master_ro_mem_interface_output dcache_mem_output_master_ro;
    slave_ro_mem_interface_input dcache_mem_input_slave_ro;
    slave_ro_mem_interface_output dcache_mem_output_slave_ro;
    master_rw_mem_interface_input dcache_mem_input_master_rw;
    master_rw_mem_interface_output dcache_mem_output_master_rw;
    slave_rw_mem_interface_input dcache_mem_input_slave_rw;
    slave_rw_mem_interface_output dcache_mem_output_slave_rw;
    master_mem_mem_interface_input dcache_mem_input_master_mem;
    master_mem_mem_interface_output dcache_mem_output_master_mem;
    
    //mem_interface icache_mem();
    master_ro_mem_interface_input icache_mem_input_master_ro;
    master_ro_mem_interface_output icache_mem_output_master_ro;
    slave_ro_mem_interface_input icache_mem_input_slave_ro;
    slave_ro_mem_interface_output icache_mem_output_slave_ro;
    master_rw_mem_interface_input icache_mem_input_master_rw;
    master_rw_mem_interface_output icache_mem_output_master_rw;
    slave_rw_mem_interface_input icache_mem_input_slave_rw;
    slave_rw_mem_interface_output icache_mem_output_slave_rw;
    master_mem_mem_interface_input icache_mem_input_master_mem;
    master_mem_mem_interface_output icache_mem_output_master_mem;
    
    //mem_interface dmmu_mem();
    master_ro_mem_interface_input dmmu_mem_input_master_ro;
    master_ro_mem_interface_output dmmu_mem_output_master_ro;
    slave_ro_mem_interface_input dmmu_mem_input_slave_ro;
    slave_ro_mem_interface_output dmmu_mem_output_slave_ro;
    master_rw_mem_interface_input dmmu_mem_input_master_rw;
    master_rw_mem_interface_output dmmu_mem_output_master_rw;
    slave_rw_mem_interface_input dmmu_mem_input_slave_rw;
    slave_rw_mem_interface_output dmmu_mem_output_slave_rw;
    master_mem_mem_interface_input dmmu_mem_input_master_mem;
    master_mem_mem_interface_output dmmu_mem_output_master_mem;
    
    //mem_interface immu_mem();
    master_ro_mem_interface_input immu_mem_input_master_ro;
    master_ro_mem_interface_output immu_mem_output_master_ro;
    slave_ro_mem_interface_input immu_mem_input_slave_ro;
    slave_ro_mem_interface_output immu_mem_output_slave_ro;
    master_rw_mem_interface_input immu_mem_input_master_rw;
    master_rw_mem_interface_output immu_mem_output_master_rw;
    slave_rw_mem_interface_input immu_mem_input_slave_rw;
    slave_rw_mem_interface_output immu_mem_output_slave_rw;
    master_mem_mem_interface_input immu_mem_input_master_mem;
    master_mem_mem_interface_output immu_mem_output_master_mem;
    
    //branch_predictor_interface bp();
    branch_predictor_branch_predictor_input bp_branch_predictor_input;
    branch_predictor_branch_predictor_output bp_branch_predictor_output;
    fetch_branch_predictor_input bp_fetch_input;
    fetch_branch_predictor_output bp_fetch_output;


    
    branch_results_t br_results;
    logic branch_flush;
    logic potential_branch_exception;
    exception_packet_t br_exception;
    logic branch_exception_is_jump;

    //ras_interface ras();
    branch_predictor_ras_interface_output ras_branch_predictor_output;
    self_ras_interface_input ras_self_input;
    self_ras_interface_output ras_self_output;
    fetch_ras_interface_input ras_fetch_input;
    fetch_ras_interface_output ras_fetch_output;


    
    issue_packet_t issue;
    //register_file_issue_interface #(.NUM_WB_GROUPS(CONFIG.NUM_WB_GROUPS), .READ_PORTS(REGFILE_READ_PORTS), .DATA_WIDTH(32)) rf_issue();
    register_file_register_file_issue_interface_input rf_issue_register_file_input;
    register_file_register_file_issue_interface_output rf_issue_register_file_output;
    issue_register_file_issue_interface_input rf_issue_issue_input;
    issue_register_file_issue_interface_output rf_issue_issue_output;
    
    //register_file_issue_interface #(.NUM_WB_GROUPS(2), .READ_PORTS(3), .DATA_WIDTH(FLEN)) fp_rf_issue();
    register_file_register_file_issue_interface_input fp_rf_issue_register_file_input;
    register_file_register_file_issue_interface_output fp_rf_issue_register_file_output;
    issue_register_file_issue_interface_input fp_rf_issue_issue_input;
    issue_register_file_issue_interface_output fp_rf_issue_issue_output;

    logic [MAX_NUM_UNITS-1:0] unit_needed;
    logic [MAX_NUM_UNITS-1:0][REGFILE_READ_PORTS-1:0] unit_uses_rs;
    logic [1:0][2:0] fp_unit_uses_rs;
    logic [MAX_NUM_UNITS-1:0] unit_uses_rd;
    logic [1:0] fp_unit_uses_rd;

    logic [31:0] constant_alu;

    //unit_issue_interface unit_issue [MAX_NUM_UNITS-1:0]();
    decode_unit_issue_interface_input unit_issue_decode_input[MAX_NUM_UNITS-1:0];
    decode_unit_issue_interface_output unit_issue_decode_output[MAX_NUM_UNITS-1:0];
    unit_unit_issue_interface_input unit_issue_unit_input[MAX_NUM_UNITS-1:0];
    unit_unit_issue_interface_output unit_issue_unit_output[MAX_NUM_UNITS-1:0];

    exception_packet_t  ls_exception;
    logic ls_exception_is_store;

    //mmu_interface immu();
    mmu_mmu_interface_input immu_mmu_input;
    mmu_mmu_interface_output immu_mmu_output;
    tlb_mmu_interface_input immu_tlb_input;
    tlb_mmu_interface_output immu_tlb_output;
    csr_mmu_interface_output immu_csr_output;

    
    //mmu_interface dmmu();
    mmu_mmu_interface_input dmmu_mmu_input;
    mmu_mmu_interface_output dmmu_mmu_output;
    tlb_mmu_interface_input dmmu_tlb_input;
    tlb_mmu_interface_output dmmu_tlb_output;
    csr_mmu_interface_output dmmu_csr_output;


    //tlb_interface itlb();
    tlb_tlb_interface_input itlb_tlb_input;
    tlb_tlb_interface_output itlb_tlb_output;
    requester_tlb_interface_output itlb_requester_output;
    requester_tlb_interface_input itlb_requester_input;

    //tlb_interface dtlb();
    tlb_tlb_interface_input dtlb_tlb_input;
    tlb_tlb_interface_output dtlb_tlb_output;
    requester_tlb_interface_output dtlb_requester_output;
    requester_tlb_interface_input dtlb_requester_input;
    
    logic instruction_translation_on;
    logic data_translation_on;
    logic [ASIDLEN-1:0] asid;

    //Instruction ID/Metadata
        //ID issuing
    id_t pc_id;
    logic pc_id_available;
    logic pc_id_assigned;
    logic [31:0] if_pc;
        //Fetch stage
    id_t fetch_id;
    logic fetch_complete;
    logic [31:0] fetch_instruction;
    logic early_branch_flush;
    logic early_branch_flush_ras_adjust;
    fetch_metadata_t fetch_metadata;
        //Decode stage
    logic decode_advance;
    decode_packet_t decode;
    logic decode_uses_rd;
    logic fp_decode_uses_rd;
    rs_addr_t decode_rd_addr;
    logic decode_is_store;
    phys_addr_t decode_phys_rd_addr;
    phys_addr_t fp_decode_phys_rd_addr;
    phys_addr_t decode_phys_rs_addr [REGFILE_READ_PORTS];
    phys_addr_t fp_decode_phys_rs_addr [3];
    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_rs_wb_group [REGFILE_READ_PORTS];
    logic fp_decode_rs_wb_group [3];
    logic [2:0] dyn_rm;

        //ID freeing
    retire_packet_t wb_retire;
    retire_packet_t fp_wb_retire;
    retire_packet_t store_retire;
    id_t retire_ids [RETIRE_PORTS];
    logic retire_port_valid [RETIRE_PORTS];
    logic [LOG2_RETIRE_PORTS : 0] retire_count;
        //Writeback
    //unit_writeback_interface #(.DATA_WIDTH(32)) unit_wb [MAX_NUM_UNITS]();
    unit_unit_writeback_interface_input unit_wb_unit_input[MAX_NUM_UNITS];
    unit_unit_writeback_interface_output unit_wb_unit_output[MAX_NUM_UNITS];
    wb_unit_writeback_interface_input unit_wb_wb_input[MAX_NUM_UNITS];
    wb_unit_writeback_interface_output unit_wb_wb_output[MAX_NUM_UNITS];
    
    //unit_writeback_interface #(.DATA_WIDTH(FLEN)) fp_unit_wb [2]();
    unit_unit_writeback_interface_input fp_unit_wb_unit_input[2];
    unit_unit_writeback_interface_output fp_unit_wb_unit_output[2];
    wb_unit_writeback_interface_input fp_unit_wb_wb_input[2];
    wb_unit_writeback_interface_output fp_unit_wb_wb_output[2];
    
    wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS];
    fp_wb_packet_t fp_wb_packet [2];
    phys_addr_t wb_phys_addr [CONFIG.NUM_WB_GROUPS];
    phys_addr_t fp_wb_phys_addr [2];
    logic [4:0] fflag_wmask;

    //renamer_interface #(.NUM_WB_GROUPS(CONFIG.NUM_WB_GROUPS), .READ_PORTS(REGFILE_READ_PORTS)) decode_rename_interface ();
    renamer_renamer_interface_input decode_rename_interface_renamer_input;
    renamer_renamer_interface_output decode_rename_interface_renamer_output;
    decode_renamer_interface_input decode_rename_interface_decode_input;
    decode_renamer_interface_output decode_rename_interface_decode_output;
    
    //renamer_interface #(.NUM_WB_GROUPS(2), .READ_PORTS(3)) fp_decode_rename_interface ();
    renamer_renamer_interface_input fp_decode_rename_interface_renamer_input;
    renamer_renamer_interface_output fp_decode_rename_interface_renamer_output;
    decode_renamer_interface_input fp_decode_rename_interface_decode_input;
    decode_renamer_interface_output fp_decode_rename_interface_decode_output;
    
    //Global Control
    //exception_interface exception [NUM_EXCEPTION_SOURCES]();
    unit_exception_output exception_output[NUM_EXCEPTION_SOURCES];
    econtrol_exception_interface_input exception_input[NUM_EXCEPTION_SOURCES];
    gc_outputs_t gc;
    tlb_packet_t sfence;
    load_store_status_t load_store_status;
    logic [LOG2_MAX_IDS:0] post_issue_count;

    logic mret;
    logic sret;
    logic csr_frontend_flush;
    logic interrupt_taken;
    logic interrupt_pending;

    //CSR broadcast info
    logic [1:0] current_privilege;
    logic tvm;
    logic tsr;
    envcfg_t menvcfg;
    envcfg_t senvcfg;
    logic [31:0] mepc;
    logic [31:0] sepc;
    logic [31:0] exception_target_pc;


    //Decode Unit and Fetch Unit
    logic issue_stage_ready;
    phys_addr_t issue_phys_rs_addr [REGFILE_READ_PORTS];
    phys_addr_t fp_issue_phys_rs_addr [3];
    rs_addr_t issue_rs_addr [REGFILE_READ_PORTS];
    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rd_wb_group;
    logic fp_issue_rd_wb_group;
    logic illegal_instruction;
    logic instruction_issued;
    logic instruction_issued_with_rd;
    logic fp_instruction_issued_with_rd;

    ////////////////////////////////////////////////////
    //Implementation



    ////////////////////////////////////////////////////
    // Memory Interface
    generate if (CONFIG.MODES == MSU || CONFIG.INCLUDE_ICACHE || CONFIG.INCLUDE_DCACHE) begin : gen_core_arb
        core_arbiter #(.INCLUDE_DCACHE(CONFIG.INCLUDE_DCACHE), .INCLUDE_ICACHE(CONFIG.INCLUDE_ICACHE), .INCLUDE_MMUS(CONFIG.MODES == MSU))
        arb(
            .clk (clk),
            .rst (rst),
            .dcache_input (dcache_mem_input_slave_rw),
            .dcache_output (dcache_mem_output_slave_rw),
            .icache_input (icache_mem_input_slave_ro),
            .icache_output (icache_mem_output_slave_ro),
            .dmmu_input (dmmu_mem_input_slave_ro),
            .dmmu_output (dmmu_mem_output_slave_ro),
            .immu_input (immu_mem_input_slave_ro),
            .immu_output (immu_mem_output_slave_ro),
            .mem_input (immu_mem_input_master_ro),
            .mem_output (immu_mem_output_master_ro)
        );
    end
    endgenerate

    ////////////////////////////////////////////////////
    // ID support
    instruction_metadata_and_id_management #(.CONFIG(CONFIG))
    id_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .pc_id (pc_id),
        .pc_id_available (pc_id_available),
        .if_pc (if_pc),
        .pc_id_assigned (pc_id_assigned),
        .fetch_id (fetch_id),
        .early_branch_flush (early_branch_flush),
        .fetch_complete (fetch_complete),
        .fetch_instruction (fetch_instruction),
        .fetch_metadata (fetch_metadata),
        .decode (decode),
        .decode_advance (decode_advance),
        .decode_uses_rd (decode_uses_rd),
        .fp_decode_uses_rd (fp_decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .fp_decode_phys_rd_addr (fp_decode_phys_rd_addr),
        .decode_is_store (decode_is_store),
        .issue (issue),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .fp_instruction_issued_with_rd (fp_instruction_issued_with_rd),
        .wb_packet (wb_packet),
        .fp_wb_packet (fp_wb_packet),
        .wb_phys_addr (wb_phys_addr),
        .fp_wb_phys_addr (fp_wb_phys_addr),
        .wb_retire (wb_retire),
        .fp_wb_retire (fp_wb_retire),
        .store_retire (store_retire),
        .retire_ids (retire_ids),
        .retire_port_valid(retire_port_valid),
        .retire_count (retire_count),
        .post_issue_count(post_issue_count)
    );

    ////////////////////////////////////////////////////
    // Fetch
    fetch # (.CONFIG(CONFIG))
    fetch_block (
        .clk (clk),
        .rst (rst),
        .branch_flush (branch_flush),
        .gc (gc),
        .pc_id (pc_id),
        .pc_id_available (pc_id_available),
        .pc_id_assigned (pc_id_assigned),
        .fetch_complete (fetch_complete),
        .fetch_metadata (fetch_metadata),
        .bp_input (bp_fetch_input),
        .bp_output (bp_fetch_output),
        .ras_input (ras_fetch_input),
        .ras_output (ras_fetch_output),
        .early_branch_flush (early_branch_flush),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .if_pc (if_pc),
        .fetch_instruction (fetch_instruction),
        .instruction_bram_input (instruction_bram_input),
        .instruction_bram_output (instruction_bram_input),
        .iwishbone_input (iwishbone_input),
        .iwishbone_output (iwishbone_output),
        .icache_on ('1),
        .tlb_input (itlb_tlb_input),
        .tlb_output (itlb_tlb_output),
        .mem_input  (icache_mem_input_master_mem),
        .mem_output (icache_mem_output_master_mem)
    );

    branch_predictor #(.CONFIG(CONFIG))
    bp_block (
        .clk (clk),
        .rst (rst),
        .bp_input (bp_branch_predictor_input),
        .bp_output (bp_branch_predictor_output),
        .br_results (br_results),
        .ras_output(ras_branch_predictor_output)
    );

    ras # (.CONFIG(CONFIG))
    ras_block(
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .ras_input (ras_self_input),
        .ras_output (ras_self_output)
    );

    itlb #(.WAYS(CONFIG.ITLB.WAYS), .DEPTH(CONFIG.ITLB.DEPTH))
    i_tlb (
        .clk (clk),
        .rst (rst),
        .translation_on (instruction_translation_on),
        .sfence (sfence),
        .abort_request (gc.fetch_flush | early_branch_flush),
        .asid (asid),
        .tlb_input (itlb_tlb_input),
        .tlb_output (itlb_tlb_output),
        .mmu_input (immu_tlb_input),
        .mmu_output (immu_tlb_output)
    );

    generate if (CONFIG.MODES == MSU) begin : gen_immu
        mmu i_mmu (
            .clk (clk),
            .rst (rst),
            .mmu_input (immu_mmu_input),
            .mmu_output (immu_mmu_output),
            .abort_request (gc.fetch_flush | early_branch_flush),
            .mem_input (immu_mem_input_master_ro),
            .mem_output (immu_mem_output_master_ro)
        );

        end
    endgenerate

    ////////////////////////////////////////////////////
    //Renamer
    renamer #(.NUM_WB_GROUPS(CONFIG.NUM_WB_GROUPS), .READ_PORTS(REGFILE_READ_PORTS), .RENAME_ZERO(0))
    renamer_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_advance (decode_advance),
        .decode_input (decode_rename_interface_renamer_input),
        .decode_output (decode_rename_interface_renamer_output),
        .issue (issue), //packet
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .wb_retire (wb_retire)
    );

    ////////////////////////////////////////////////////
    //Decode/Issue
    decode_and_issue #(.CONFIG(CONFIG))
    decode_and_issue_block (
        .clk (clk),
        .rst (rst),
        .pc_id_available (pc_id_available),
        .decode (decode),
        .decode_advance (decode_advance),
        .unit_needed (unit_needed),
        .unit_uses_rs (unit_uses_rs),
        .fp_unit_uses_rs (fp_unit_uses_rs),
        .unit_uses_rd (unit_uses_rd),
        .fp_unit_uses_rd (fp_unit_uses_rd),
        .renamer_input (decode_rename_interface_decode_input),
        .renamer_output (decode_rename_interface_decode_output),
        .fp_renamer_input (fp_decode_rename_interface_decode_input),
        .fp_renamer_output (fp_decode_rename_interface_decode_output),
        .decode_uses_rd (decode_uses_rd),
        .fp_decode_uses_rd (fp_decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .fp_decode_phys_rd_addr (fp_decode_phys_rd_addr),
        .decode_phys_rs_addr (decode_phys_rs_addr),
        .fp_decode_phys_rs_addr (fp_decode_phys_rs_addr),
        .decode_rs_wb_group (decode_rs_wb_group),
        .fp_decode_rs_wb_group (fp_decode_rs_wb_group),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .fp_instruction_issued_with_rd (fp_instruction_issued_with_rd),
        .issue (issue),
        .issue_rs_addr (issue_rs_addr),
        .issue_stage_ready (issue_stage_ready),
        .issue_phys_rs_addr (issue_phys_rs_addr),
        .fp_issue_phys_rs_addr (fp_issue_phys_rs_addr),
        .issue_rd_wb_group (issue_rd_wb_group),
        .fp_issue_rd_wb_group (fp_issue_rd_wb_group),
        .rf_input (rf_issue_issue_input),
        .rf_output (rf_issue_issue_output),
        .fp_rf_input (fp_rf_issue_issue_input),
        .fp_rf_output (fp_rf_issue_issue_output),
        .constant_alu (constant_alu),
        .unit_issue_input (unit_issue_decode_input),
        .unit_issue_output (unit_issue_decode_output),
        .gc (gc),
        .current_privilege (current_privilege),
        .exception (exception_output[PRE_ISSUE_EXCEPTION])
    );

    ////////////////////////////////////////////////////
    //Register File
    register_file #(.NUM_WB_GROUPS(CONFIG.NUM_WB_GROUPS), .READ_PORTS(REGFILE_READ_PORTS), .PORT_ZERO_ABSENT(0), .USE_ZERO(0), .WB_PACKET_TYPE(wb_packet_t))
    register_file_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_phys_rs_addr (decode_phys_rs_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .decode_rs_wb_group (decode_rs_wb_group),
        .decode_advance (decode_advance),
        .decode_uses_rd (decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .rf_issue_input (rf_issue_register_file_input),
        -rf_issue_output (rf_issue_register_file_output),
        .commit (wb_packet),
        .wb_phys_addr (wb_phys_addr)
    );

    ////////////////////////////////////////////////////
    //Execution Units
    branch_unit #(.CONFIG(CONFIG))
    branch_unit_block (
        .clk (clk),
        .rst (rst),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[BR_ID]),
        .uses_rs (unit_uses_rs[BR_ID]),
        .uses_rd (unit_uses_rd[BR_ID]),
        .rf (rf_issue_issue_input.data),
        .constant_alu (constant_alu), 
        .issue_input (unit_issue_unit_input[BR_ID]),
        .issue_output (unit_issue_unit_output[BR_ID]),
        .br_results (br_results),
        .branch_flush (branch_flush),
        .exception_output (exception[BR_EXCEPTION])
    );


    alu_unit alu_unit_block (
        .clk (clk),
        .rst (rst),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[ALU_ID]),
        .uses_rs (unit_uses_rs[ALU_ID]),
        .uses_rd (unit_uses_rd[ALU_ID]),
        .rf (rf_issue_issue_input.data),
        .constant_alu (constant_alu),
        .issue_rs_addr (issue_rs_addr),
        .issue_input (unit_issue_unit_input[ALU_ID]),
        .issue_output (unit_issue_unit_input[ALU_ID]),
        .wb_input (unit_wb_unit_input[ALU_ID]),
        .wb_output (unit_wb_unit_output[ALU_ID])
    );

    load_store_unit #(.CONFIG(CONFIG))
    load_store_unit_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[LS_ID]),
        .uses_rs (unit_uses_rs[LS_ID]),
        .fp_uses_rs (fp_unit_uses_rs[0]),
        .uses_rd (unit_uses_rd[LS_ID]),
        .fp_uses_rd (fp_unit_uses_rd[0]),
        .decode_is_store (decode_is_store),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .fp_instruction_issued_with_rd (fp_instruction_issued_with_rd),
        .issue_rs_addr (issue_rs_addr),
        .issue_rd_wb_group (issue_rd_wb_group),
        .fp_issue_rd_wb_group (fp_issue_rd_wb_group),
        .rs2_inuse (rf_issue_issue_input.inuse[RS2]),
        .fp_rs2_inuse (fp_ rf_issue_issue_input.inuse[RS2]),
        .rf (rf_issue_issue_input.data),
        .fp_rf (fp_rf_issue_issue_input.data),
        .issue_input (unit_issue_unit_input[LS_ID]),
        .issue_output (unit_issue_unit_output[LS_ID]),
        .dcache_on (1'b1),
        .clear_reservation (1'b0),
        .tlb_input (dtlb_requester_input),
        -tlb_output (dtlb_requester_output),
        .mem_input (dcache_mem_input_master_rw),
        .mem_output (dcache_mem_output_master_rw),
        .m_axi_input (m_axi_input),
        .m_axi_output (m_axi_output),
        .m_avalon_input (m_avalon_input),
        .m_avalon_output (m_avalon_output),
        .dwishbone_input (dwishbone_input),
        .dwishbone_output (dwishbone_output),
        .data_bram_input (data_bram_input),
        .data_bram_output (data_bram_ouput),
        .current_privilege (current_privilege),
        .menvcfg (menvcfg),
        .senvcfg (senvcfg),
        .wb_packet (wb_packet),
        .fp_wb_packet (fp_wb_packet),
        .retire_id (retire_ids[0]),
        .store_retire (store_retire),
        .exception_output (exception_output[LS_EXCEPTION]),
        .load_store_status(load_store_status),
        .wb_input (unit_wb_unit_input[LS_ID]),
        .wb_output (unit_wb_unit_output[LS_ID]),
        .fp_wb_input (fp_unit_wb_unit_input[LS_ID]),
        .fp_wb_output (fp_unit_wb_unit_output[LS_ID])
    );

    dtlb #(.WAYS(CONFIG.DTLB.WAYS), .DEPTH(CONFIG.DTLB.DEPTH))
    d_tlb (
        .clk (clk),
        .rst (rst),
        .translation_on (data_translation_on),
        .sfence (sfence),
        .asid (asid),
        .tlb_input (dtlb_tlb_input),
        .tlb_output (dtlb_tlb_output),
        .mmu_input (dmmu_tlb_input),
        .mmu_output (dmmu_tlb_output)
    );

    generate if (CONFIG.MODES == MSU) begin : gen_dmmu
        mmu d_mmu (
            .clk (clk),
            .rst (rst),
            .mmu_input (dmmu_mmu_input),
            .mmu_output (dmmu_mmu_output),
            .abort_request (1'b0),
            .mem_input (dmmu_mem_input_master_ro),
            .mem_output (dmmu_mem_output_master_ro)
        );
    end
    endgenerate

    generate if (CONFIG.INCLUDE_UNIT.CSR) begin : gen_csrs
        csr_unit # (.CONFIG(CONFIG))
        csr_unit_block (
            .clk(clk),
            .rst(rst),
            .decode_stage (decode),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .issue_rs_addr (issue_rs_addr),
            .unit_needed (unit_needed[CSR_ID]),
            .uses_rs (unit_uses_rs[CSR_ID]),
            .uses_rd (unit_uses_rd[CSR_ID]),
            .rf (rf_issue_issue_input.data),
            .instruction_issued (instruction_issued),
            .fp_instruction_issued_with_rd (fp_instruction_issued_with_rd),
            .issue_input (unit_issue_unit_input[CSR_ID]),
            .issue_output (unit_issue_unit_output[CSR_ID]),
            .wb_input (unit_wb_unit_input[CSR_ID]),
            .wb_output (unit_wb_unit_output[CSR_ID]),
            .current_privilege(current_privilege),
            .menvcfg(menvcfg),
            .senvcfg(senvcfg),
            .fflag_wmask (fflag_wmask),
            .dyn_rm (dyn_rm),
            .interrupt_taken(interrupt_taken),
            .interrupt_pending(interrupt_pending),
            .csr_frontend_flush(csr_frontend_flush),
            .instruction_translation_on(instruction_translation_on),
            .data_translation_on(data_translation_on),
            .asid(asid),
            .immu_output(immu_csr_output),
            .dmmu_output(dmmu_csr_output),
            .exception_pkt(gc.exception),
            .exception_target_pc (exception_target_pc),
            .mret(mret),
            .sret(sret),
            .mepc(mepc),
            .sepc(sepc),
            .exception_output(exception_output[CSR_EXCEPTION]),
            .retire_ids(retire_ids),
            .mtime(mtime),
            .s_interrupt(s_interrupt),
            .m_interrupt(m_interrupt)
        );
    end endgenerate

    gc_unit #(.CONFIG(CONFIG))
    gc_unit_block (
        .clk (clk),
        .rst (rst),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[GC_ID]),
        .uses_rs (unit_uses_rs[GC_ID]),
        .uses_rd (unit_uses_rd[GC_ID]),
        .instruction_issued (instruction_issued),
        .constant_alu (constant_alu),
        .rf (rf_issue_issue_input.data),
        .issue_input (unit_issue_unit_input[GC_ID]),
        .issue_output (unit_issue_unit_output[GC_ID]),
        .branch_flush (branch_flush),
        .local_gc_exception_output (exception_output[GC_EXCEPTION]),
        .exception_input (exception_input),
        .exception_target_pc (exception_target_pc),
        .csr_frontend_flush (csr_frontend_flush),
        .current_privilege (current_privilege),
        .tvm (tvm),
        .tsr (tsr),
        .gc (gc),
        .sfence (sfence),
        .mret(mret),
        .sret(sret),
        .mepc(mepc),
        .sepc(sepc),
        .interrupt_taken(interrupt_taken),
        .interrupt_pending(interrupt_pending),
        .load_store_status(load_store_status)
    );

    generate if (CONFIG.INCLUDE_UNIT.MUL) begin : gen_mul
        mul_unit mul_unit_block (
            .clk (clk),
            .rst (rst),
            .decode_stage (decode),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .unit_needed (unit_needed[MUL_ID]),
            .uses_rs (unit_uses_rs[MUL_ID]),
            .uses_rd (unit_uses_rd[MUL_ID]),
            .rf (rf_issue_issue_input.data),
            .issue_input (unit_issue_unit_input[MUL_ID]),
            .issue_output (unit_issue_unit_output[MUL_ID]),
            .wb_input (unit_wb_unit_input[MUL_ID]),
            .wb_output (unit_wb_unit_output[MUL_ID])
        );
    end endgenerate

    generate if (CONFIG.INCLUDE_UNIT.DIV) begin : gen_div
        div_unit div_unit_block (
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .instruction_issued_with_rd (instruction_issued_with_rd),
            .decode_stage (decode),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .issue_rs_addr (issue_rs_addr),
            .unit_needed (unit_needed[DIV_ID]),
            .uses_rs (unit_uses_rs[DIV_ID]),
            .uses_rd (unit_uses_rd[DIV_ID]),
            .rf (rf_issue_issue_input.data),
            .issue_input (unit_issue_unit_input[DIV_ID]),
            .issue_output (unit_issue_unit_output[DIV_ID]),
            .wb_input (unit_wb_unit_input[DIV_ID]),
            .wb_output (unit_wb_unit_output[DIV_ID])
        );
    end endgenerate


    generate if (CONFIG.INCLUDE_UNIT.CUSTOM) begin : gen_custom
        custom_unit custom_unit_block (
            .clk (clk),
            .rst (rst),
            .decode_stage (decode),
            .unit_needed (unit_needed[CUSTOM_ID]),
            .uses_rs (unit_uses_rs[CUSTOM_ID]),
            .uses_rd (unit_uses_rd[CUSTOM_ID]),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .rf (rf_issue_issue_input.data),
            .issue_input (unit_issue_unit_input[CUSTOM_ID]),
            .issue_output (unit_issue_unit_output[CUSTOM_ID]),
            .wb_input (unit_wb_unit_input[CUSTOM_ID]),
            .wb_output (unit_wb_unit_output[CUSTOM_ID])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Writeback
    generate for (genvar i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin : gen_wb
        writeback #(
            .NUM_WB_UNITS (get_num_wb_units(CONFIG.WB_GROUP[i])),
            .WB_INDEX (CONFIG.WB_GROUP[i])
        )
        writeback_block (
            .wb_packet (wb_packet[i]),
            .unit_wb_input (unit_wb_wb_input),
            .unit_wb_output (unit_wb_wb_output)
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //FPU
    generate if (CONFIG.INCLUDE_UNIT.FPU) begin : gen_fpu

        fp_writeback fp_writeback_block (
            .unit_wb_input (fp_unit_wb_wb_input),
            .unit_wb_output (fp_unit_wb_wb_output),
            .wb_packet (fp_wb_packet)
        );

        fpu_top #(.CONFIG(CONFIG))
        fpu_block (
            .clk (clk),
            .rst (rst),
            .decode_stage (decode),
            .unit_needed (unit_needed[FPU_ID]),
            .uses_rs (unit_uses_rs[FPU_ID]),
            .fp_uses_rs (fp_unit_uses_rs[1]),
            .uses_rd (unit_uses_rd[FPU_ID]),
            .fp_uses_rd (fp_unit_uses_rd[1]),
            .issue_stage_ready (issue_stage_ready),
            .dyn_rm (dyn_rm),
            .int_rf (rf_issue_issue_input.data),
            .fp_rf (fp_rf_issue_issue_input.data),
            .issue_input (unit_issue_unit_input[FPU_ID]),
            .issue_output (unit_issue_unit_output[FPU_ID]),
            .int_wb_input (unit_wb_unit_input[FPU_ID]),
            .int_wb_output (unit_wb_unit_output[FPU_ID]),
            .fp_wb_input (fp_unit_wb_unit_input[1]),
            .fp_wb_output (fp_unit_wb_unit_output[1]),
            .fflags (fflag_wmask)
        );

        register_file #(.NUM_WB_GROUPS(2), .READ_PORTS(3), .USE_ZERO(1), .PORT_ZERO_ABSENT(1), .WB_PACKET_TYPE(fp_wb_packet_t))
        fp_register_file_block (
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .decode_phys_rs_addr (fp_decode_phys_rs_addr),
            .decode_phys_rd_addr (fp_decode_phys_rd_addr),
            .decode_rs_wb_group (fp_decode_rs_wb_group),
            .decode_advance (decode_advance),
            .decode_uses_rd (fp_decode_uses_rd),
            .decode_rd_addr ('x),
            .rf_issue_input (fp_rf_issue_register_file_input),
            -rf_issue_output (fp_rf_issue_register_file_output),
            .commit (fp_wb_packet),
            .wb_phys_addr (fp_wb_phys_addr)
        );

        renamer #(.NUM_WB_GROUPS(2), .READ_PORTS(3), .RENAME_ZERO(1))
        fp_renamer_block (
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .decode_advance (decode_advance),
            .decode_input (fp_decode_rename_interface_renamer_input),
            .decode_output (fp_decode_rename_interface_renamer_output),
            .issue (issue),
            .instruction_issued_with_rd (fp_instruction_issued_with_rd),
            .wb_retire (fp_wb_retire)
        );

    end endgenerate

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions


endmodule
