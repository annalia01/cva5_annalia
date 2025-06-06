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

module fp_madd_wrapper

    import cva5_config::*;
    import fpu_types::*;
    import cva5_types::*;

    #(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    (
        input logic clk,
        input logic rst,
        input fp_madd_inputs_t args,
        //unit_issue_interface.unit issue,
        unit_unit_issue_interface_input issue_input,
        unit_unit_issue_interface_output issue_output,
        
        //fp_intermediate_wb_interface.unit madd_wb,
        fp_intermediate_wb_interface_unit_input madd_wb_input,
        fp_intermediate_wb_interface_unit_output madd_wb_output,
        
        //fp_intermediate_wb_interface.unit mul_wb
        fp_intermediate_wb_interface_unit_input mul_wb_input,
        fp_intermediate_wb_interface_unit_output mul_wb_output
    );

    //unit_issue_interface mul_issue();
    decode_unit_issue_interface_input mul_issue_decode_input;
    decode_unit_issue_interface_output mul_issue_decode_output;
    unit_unit_issue_interface_input mul_issue_unit_input;
    unit_unit_issue_interface_output mul_issue_unit_output;
    
    //unit_issue_interface add_issue();
    decode_unit_issue_interface_input add_issue_decode_input;
    decode_unit_issue_interface_output add_issue_decode_output;
    unit_unit_issue_interface_input add_issue_unit_input;
    unit_unit_issue_interface_output add_issue_unit_output;

    /////////////////////////////////////////////
    //Multiplication unit
    //Writes back multiplication instructions directly with its own port
    //Generates FMA operands
    fp_add_inputs_t fma_mul_outputs;
    logic fma_valid;
    logic fma_valid_r;
    logic fma_advance;
    id_t fma_id;
    assign fma_advance = ~fma_valid_r | add_issue_decode_input.ready;

    assign mul_issue_decode_output.new_request = ~args.add & issue_input.new_request;
    assign mul_issue_decode_output.id = issue_input.id;
    fp_mul #(.CONFIG(CONFIG)) mul_core (
        .mul_args(args.mul_args),
        .fma(args.fma),
        .fma_args(args.fma_args),
        .issue_input(mul_issue_unit_input),
        .issue_output(mul_issue_unit_output),
        .wb_input(mul_wb_input),
        .wb_output(mul_wb_output),
        .add_ready(fma_advance),
        .add_valid(fma_valid),
        .add_id(fma_id),
        .add_args(fma_mul_outputs),
    .*);

    //It would probably be possible to use these directly without registering if some of the exponent logic in the multiplier was pushed to an earlier cycle
    fp_add_inputs_t fma_mul_outputs_r;
    id_t fma_id_r;
    always_ff @(posedge clk) begin
        if (rst)
            fma_valid_r <= 0;
        else if (fma_advance)
            fma_valid_r <= fma_valid;
        if (fma_advance) begin
            fma_id_r <= fma_id;
            fma_mul_outputs_r <= fma_mul_outputs;
        end
    end

    /////////////////////////////////////////////
    //Addition unit
    //Input comes from FMA or add instructions, prioritizing FMA
    //FMA inputs are the registered outputs from the multiplier
    fp_add_inputs_t add_inputs;
    assign add_inputs = fma_valid_r ? fma_mul_outputs_r : args.add_args;
    assign add_issue_decode_output.id = fma_valid_r ? fma_id_r : issue_input.id;
    assign add_issue_decode_output.new_request = fma_valid_r | (issue_input.new_request & args.add);

    fp_add add_core (
        .args(add_inputs),
        .issue(add_issue_unit_input),
        .issue_output(add_issue_unit_output),
        .wb_input(madd_wb_input),
        .wb_output(madd_wb_output),
    .*);

    assign issue_output.ready = (~args.add & mul_issue_unit_output.ready) | (args.add & add_issue_unit_output.ready & ~fma_valid_r);

endmodule
