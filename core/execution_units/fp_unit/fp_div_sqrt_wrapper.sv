/*
 * Copyright © 2019-2023 Yuhui Gao, Chris Keilbart, Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module fp_div_sqrt_wrapper

    import cva5_config::*;
    import fpu_types::*;

    (
        input logic clk,
        input logic rst,
        input fp_div_inputs_t div_inputs,
        input fp_sqrt_inputs_t sqrt_inputs,
        //unit_issue_interface.unit div_issue,
        unit_unit_issue_interface_input div_issue_input,
        unit_unit_issue_interface_output div_issue_output,
        
        //unit_issue_interface.unit sqrt_issue,
        unit_unit_issue_interface_input sqrt_issue_input,
        unit_unit_issue_interface_output sqrt_issue_output,
        
        //fp_intermediate_wb_interface.unit wb
        fp_intermediate_wb_interface_unit_input wb_input,
        fp_intermediate_wb_interface_unit_output wb_output
    );

    //fp_intermediate_wb_interface div_wb();
    fp_intermediate_wb_interface_unit_input div_wb_unit_input;
    fp_intermediate_wb_interface_unit_output div_wb_unit_output;
    fp_intermediate_wb_interface_wb_input div_wb_wb_input;
    fp_intermediate_wb_interface_wb_output div_wb_wb_output;
    
    //fp_intermediate_wb_interface sqrt_wb();
    fp_intermediate_wb_interface_unit_input sqrt_wb_unit_input;
    fp_intermediate_wb_interface_unit_output sqrt_wb_unit_output;
    fp_intermediate_wb_interface_wb_input sqrt_wb_wb_input;
    fp_intermediate_wb_interface_wb_output sqrt_wb_wb_output;

    ////////////////////////////////////////////////////
    //Implementation
    //Div/Sqrt with distinct issue
    //Shared writeback
    fp_div div (
        .args(div_inputs),
        .issue_input(div_issue_input),
        .issue_output(div_issue_output),
        .wb_input(div_wb_unit_input),
        .wb_output(div_wb_unit_output),
    .*);

    fp_sqrt sqrt (
        .args(sqrt_inputs),
        .issue_input(sqrt_issue_input),
        .issue_output(sqrt_issue_output),
        .wb_unit_input(sqrt_wb_unit_input),
        .wb_unit_output(sqrt_wb_unit_output),
    .*);

    //SQRT has higher priority on ties because of longer latency
    always_comb begin
        sqrt_wb_wb_output.ack = wb_input.ack & sqrt_wb_wb_input.done;
        div_wb_wb_output.ack = wb_input.ack & ~sqrt_wb_wb_input.done;
        
        if (sqrt_wb_wb_input.done) begin
            wb_output.id = sqrt_wb_wb_input.id;
            wb_output.done = 1;
            wb_output.rd = sqrt_wb_wb_input.rd;
            wb_output.expo_overflow = sqrt_wb_wb_input.expo_overflow;
            wb_output.fflags = sqrt_wb_wb_input.fflags;
            wb_output.rm = sqrt_wb_wb_input.rm;
            wb_output.carry = sqrt_wb_wb_input.carry;
            wb_output.safe = sqrt_wb_wb_input.safe;
            wb_output.hidden = sqrt_wb_wb_input.hidden;
            //Collapse sticky - this saves a wide 2:1 mux
            wb_output.grs[GRS_WIDTH-1-:2] = sqrt_wb_wb_input.grs[GRS_WIDTH-1-:2];
            wb_output.grs[GRS_WIDTH-3] = |sqrt_wb_wb_input.grs[GRS_WIDTH-3:0];
            wb_output.grs[GRS_WIDTH-4:0] = '0;
            wb_output.clz = sqrt_wb_wb_input.clz;
            wb_output.right_shift = sqrt_wb_wb_input.right_shift;
            wb_output.right_shift_amt = sqrt_wb_wb_input.right_shift_amt;
            wb_output.subnormal = sqrt_wb_wb_input.subnormal;
            wb_output.ignore_max_expo = sqrt_wb_wb_input.ignore_max_expo;
            wb_output.d2s = sqrt_wb_wb_input.d2s;
        end else begin
            wb_output.id = div_wb_wb_input.id;
            wb_output.done = div_wb_wb_input.done;
            wb_output.rd = div_wb_wb_input.rd;
            wb_output.expo_overflow = div_wb_wb_input.expo_overflow;
            wb_output.fflags = div_wb_wb_input.fflags;
            wb_output.rm = div_wb_wb_input.rm;
            wb_output.carry = div_wb_wb_input.carry;
            wb_output.safe = div_wb_wb_input.safe;
            wb_output.hidden = div_wb_wb_input.hidden;
            //Collapse sticky - this saves a wide 2:1 mux
            wb_output.grs[GRS_WIDTH-1-:3] = div_wb_wb_input.grs[GRS_WIDTH-1-:3]; //Preserve MSB sticky because there can be a left shift of 1
            wb_output.grs[GRS_WIDTH-4] = |div_wb_wb_input.grs[GRS_WIDTH-4:0];
            wb_output.grs[GRS_WIDTH-5:0] = '0;
            wb_output.clz = div_wb_wb_input.clz;
            wb_output.right_shift = div_wb_wb_input.right_shift;
            wb_output.right_shift_amt = div_wb_wb_input.right_shift_amt;
            wb_output.subnormal = div_wb_wb_input.subnormal;
            wb_output.ignore_max_expo = div_wb_wb_input.ignore_max_expo;
            wb_output.d2s = div_wb_wb_input.d2s;
        end
    end

endmodule
