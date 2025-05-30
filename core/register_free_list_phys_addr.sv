/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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

/*
 *  FIFOs Not underflow/overflow safe.
 *  Intended for small FIFO depths.
 *  For continuous operation when full, enqueing side must inspect pop signal
 */
module register_free_list_phys_addr

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    #(
        parameter type DATA_TYPE = logic,
        parameter FIFO_DEPTH = 4
    )
    (
        input logic clk,
        input logic rst,
        //fifo_interface.structure fifo,
        structure_fifo_interface_input_phys_addr fifo_input,
        structure_fifo_interface_output_phys_addr fifo_output,
        input logic rollback
    );

    localparam LOG2_FIFO_DEPTH = $clog2(FIFO_DEPTH);

    //Force FIFO depth to next power of 2
    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(DATA_TYPE)-1:0] lut_ram [(2**LOG2_FIFO_DEPTH)];
    logic [LOG2_FIFO_DEPTH-1:0] write_index;
    logic [LOG2_FIFO_DEPTH-1:0] read_index;
    logic [LOG2_FIFO_DEPTH:0] inflight_count;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Occupancy Tracking
    always_ff @ (posedge clk) begin
        if (rst)
            inflight_count <= 0;
        else
            inflight_count <= inflight_count 
            + (LOG2_FIFO_DEPTH+1)'(fifo_input.pop) 
            - (LOG2_FIFO_DEPTH+1)'(fifo_input.push) 
            - (LOG2_FIFO_DEPTH+1)'(rollback);
    end

    assign fifo_output.valid = inflight_count[LOG2_FIFO_DEPTH];
    assign fifo_output.full = fifo_output.valid & ~|inflight_count[LOG2_FIFO_DEPTH-1:0];

    always_ff @ (posedge clk) begin
        if (rst) begin
            read_index <= '0;
            write_index <= '0;
        end
        else begin
            read_index <= read_index + LOG2_FIFO_DEPTH'(fifo.pop) - LOG2_FIFO_DEPTH'(rollback);
            write_index <= write_index + LOG2_FIFO_DEPTH'(fifo.push);
        end
    end

    always_ff @ (posedge clk) begin
        if (fifo_input.potential_push)
            lut_ram[write_index] <= fifo_input.data_in;
    end
    assign fifo_output.data_out = lut_ram[read_index];

    ////////////////////////////////////////////////////
    //Assertions
    fifo_overflow_assertion:
    assert property (@(posedge clk) disable iff (rst) fifo_input.push |-> (~fifo_output.full | fifo_input.pop)) else $error("overflow");
    fifo_underflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo_input.pop |-> fifo_output.valid) else $error("underflow");

endmodule
