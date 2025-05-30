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
 
module ras

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,
        input logic early_branch_flush_ras_adjust,
        //ras_interface.self ras
        self_ras_interface_input ras_input,
        self_ras_interface_output ras_output
    );

    localparam RAS_DEPTH_W = $clog2(CONFIG.BP.RAS_ENTRIES);
    logic [RAS_DEPTH_W-1:0] read_index;
    logic [RAS_DEPTH_W-1:0] new_index;
    //fifo_interface #(.DATA_TYPE(logic[RAS_DEPTH_W-1:0])) ri_fifo();
     ///////////////////////////////////////////////////////

    enqueue_fifo_interface_input ri_fifo_enqueue_input;
    enqueue_fifo_interface_output_ras ri_fifo_enqueue_output;
    dequeue_fifo_interface_input_ras ri_fifo_dequeue_input;
    dequeue_fifo_interface_output ri_fifo_dequeue_output;
    structure_fifo_interface_input_ras ri_fifo_structure_input;
    structure_fifo_interface_output_ras ri_fifo_structure_output;


 
    //On a speculative branch, save the current stack pointer
    //Restored if branch is misspredicted (gc_fetch_flush)
    cva5_fifo_ras #(.DATA_TYPE(logic[RAS_DEPTH_W-1:0]), .FIFO_DEPTH(MAX_IDS))
    read_index_fifo (
        .clk,
        .rst(rst | gc.fetch_flush | early_branch_flush_ras_adjust),
        .fifo_input(ri_fifo_structure_input),
     .fifo_output(ri_fifo_structure_output)
    );

    assign ri_fifo_enqueue_output.data_in = read_index;
    assign ri_fifo_enqueue_output.push = ras_input.branch_fetched;
    assign ri_fifo_enqueue_output.potential_push = ras_input.branch_fetched;
    assign ri_fifo_dequeue_output.pop = ras_input.branch_retired & ri_fifo_dequeue_input.valid; //Prevent popping from fifo if reset due to early_branch_flush_ras_adjust

    lutram_1w_1r #(.DATA_TYPE(logic[31:0]), .DEPTH(CONFIG.BP.RAS_ENTRIES))
    ras_stack (
        .clk(clk),
        .waddr(new_index),
        .raddr(read_index),
     .ram_write(ras_input.push),
     .new_ram_data(ras_input.new_addr),
     .ram_data_out(ras_output.addr)
    );

    //Rolls over when full, most recent calls will be correct, but calls greater than depth
    //will be lost.
    logic [RAS_DEPTH_W-1:0] new_index_base;
 assign new_index_base = (gc.fetch_flush & ri_fifo_dequeue_input.valid) ? ri_fifo_dequeue_input.data_out : read_index;
 assign new_index = new_index_base + RAS_DEPTH_W'(ras_input.push) - RAS_DEPTH_W'(ras_input.pop);
    always_ff @ (posedge clk) begin
        read_index <= new_index;
    end

endmodule
