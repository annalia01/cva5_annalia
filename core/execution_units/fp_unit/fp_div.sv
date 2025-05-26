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

module fp_div

    import cva5_config::*;
    import fpu_types::*;

    (
        input logic clk,
        input logic rst,
        input fp_div_inputs_t args,
        
        //unit_issue_interface.unit issue,
        unit_unit_issue_interface_input issue_input,
        unit_unit_issue_interface_output issue_output,
        
        //fp_intermediate_wb_interface.unit wb
        fp_intermediate_wb_interface_unit_input wb_input,
        fp_intermediate_wb_interface_unit_output wb_output
        
    );

    //unsigned_division_interface #(.DATA_WIDTH(FRAC_WIDTH+3)) div();
    unsigned_division_interface_requester_input div_requester_input;
    unsigned_division_interface_requester_output div_requester_output;
    unsigned_division_interface_divider_input div_divider_input;
    unsigned_division_interface_divider_output div_divider_output;
    ////////////////////////////////////////////////////
    //Implementation
    //Iterative divider core, bypassed on special cases
    logic result_sign;
    logic busy;
    logic new_request_r;
    assign issue_output.ready = ~busy | wb_input.ack;

    always_ff @(posedge clk) begin
        if (rst) begin
            busy <= 0;
            new_request_r <= 0;
        end
        else begin
            if (wb_input.ack)
                busy <= 0;
            if (issue_input.new_request)
                busy <= 1;
            new_request_r <= issue_input.new_request;
        end
        if (issue_input.new_request)
            result_sign <= args.rs1.d.sign ^ args.rs2.d.sign;
    end

    ////////////////////////////////////////////////////
    //Special cases
    //Edge cases like NaN, infinity, and zero don't require division so return immediately
    logic nv, nv_r;
    logic dz, dz_r;
    logic qnan, qnan_r;
    logic inf;
    logic zero, zero_r;
    logic early_exit;
    fp_t special_result;
    
    //Special case handling
    assign nv = (args.rs1_special_case.zero & args.rs2_special_case.zero) | (args.rs1_special_case.inf & args.rs2_special_case.inf) | args.rs1_special_case.snan | args.rs2_special_case.snan;
    assign dz = ~|args.rs1_special_case & args.rs2_special_case.zero;
    assign qnan = nv | args.rs1_special_case.qnan | args.rs2_special_case.qnan;
    assign inf = ~qnan & (dz | args.rs1_special_case.inf);
    assign zero = ~qnan & (args.rs1_special_case.zero | args.rs2_special_case.inf);

    always_ff @(posedge clk) begin
        if (rst)
            early_exit <= 0;
        else if (wb_input.ack)
            early_exit <= 0;
        else if (issue_input.new_request)
            early_exit <= qnan | inf | zero;
        
        if (issue_input.new_request) begin
            nv_r <= nv;
            dz_r <= dz;
            qnan_r <= qnan;
            zero_r <= zero;
        end
    end
    
    always_comb begin
        if (zero_r) begin
            special_result.d.sign = result_sign;
            special_result.raw[FLEN-2:0] = '0;
        end
        else if (qnan_r)
            special_result.raw = CANONICAL_NAN;
        else begin
            special_result.d.sign = result_sign;
            special_result.d.expo = '1;
            special_result.d.frac = '0;
        end  
    end

    ////////////////////////////////////////////////////
    //Mantissa division core
    //Designed to be swappable (though note that only a subset of the division interface ports are used)
    //Operates on normalized values and width is extended to compute guard/round/sticky
    logic result_hidden;
    frac_d_t result_frac;
    logic[1:0] result_gr;
    fp_shift_amt_t left_shift_amt;

    assign div_requester_output.dividend = {1'b1, args.rs1.d.frac, 2'b0};
    assign div_requester_output.divisor = {1'b1, args.rs2.d.frac, 2'b0};
    assign div_requester_output.start = issue_input.new_request & ~(qnan | inf | zero); //start div only if no special cases
    assign {result_hidden, result_frac, result_gr} = div_requester_input.quotient;
    fp_div_core div_core (
        .div_input(div_divider_input),
        .div_output(div_divider_output)
    .*);

    //Calculate CLZ: because 0.5 < result < 2, the shift amount is either 0 or 1
    assign left_shift_amt[EXPO_WIDTH-1:1] = '0;
    assign left_shift_amt[0] = ~result_hidden;

    ////////////////////////////////////////////////////
    //Exponent handling
    //Subtract exponents
    //Special considerations for subnormal numbers
    logic right_shift;
    fp_shift_amt_t right_shift_amt;
    logic[EXPO_WIDTH+1:0] expo_intermediate;
    logic[EXPO_WIDTH+1:0] expo_intermediate_r;
    
    assign expo_intermediate =
        ({1'b0, args.rs1.d.expo} + {{EXPO_WIDTH{1'b0}}, ~args.rs1_hidden} - {1'b0, args.rs1_prenormalize_shift_amt}) -
        ({1'b0, args.rs2.d.expo} + {{EXPO_WIDTH{1'b0}}, ~args.rs2_hidden} - {1'b0, args.rs2_prenormalize_shift_amt})
        + BIAS;

    assign right_shift = expo_intermediate_r[EXPO_WIDTH+1] | (~|expo_intermediate_r[EXPO_WIDTH:1] & ((~result_hidden & expo_intermediate_r[0]) | ~expo_intermediate_r[0]));
    assign right_shift_amt = ~expo_intermediate_r[EXPO_WIDTH-1:0] + 2;

    always_ff @(posedge clk) begin
        if (issue_input.new_request)
            expo_intermediate_r <= expo_intermediate;
    end


    ////////////////////////////////////////////////////
    //Output management
    //Either return the early execute values on cycle 1, or the regular values once the divider finishes
    logic div_hold;
    assign wb_output.done = div_divider_output.done | div_hold | early_exit;

    always_ff @(posedge clk) begin
        if (rst)
            div_hold <= 0;
        else
            div_hold <= ~wb_input.ack & (div_divider_output.done | div_hold);
    end
    
    always_ff @(posedge clk) begin
        if (issue_input.new_request) begin
            wb_output.id <= issue_output.id;
            wb_output.rm <= args.rm;
            wb_output.d2s <= args.single;
        end
    end

    always_comb begin
        if (new_request_r)
            wb_output.rd = special_result;
        else begin
            wb_output.rd.d.sign = result_sign;
            wb_output.rd.d.expo = expo_intermediate_r[EXPO_WIDTH-1:0];
            wb_output.rd.d.frac = result_frac;
        end
    end
    //Note that this overflow detection also captures subnormal numbers but they are ignored when subnormal is set
    assign wb_output.expo_overflow = expo_intermediate_r[EXPO_WIDTH] & ~new_request_r;
    assign wb_output.fflags.nv = nv_r;
    assign wb_output.fflags.dz = dz_r;
    //Set in writeback
    assign wb_output.fflags.of = 0;
    assign wb_output.fflags.uf = 0;
    assign wb_output.fflags.nx = 0;
    assign wb_output.carry = 0;
    assign wb_output.safe = 0;
    assign wb_output.hidden = (new_request_r & ~zero_r) | (~new_request_r & result_hidden);
    assign wb_output.grs = new_request_r ? '0 : {result_gr, div_requester_input.remainder, {(GRS_WIDTH-FRAC_WIDTH-5){1'b0}}};
    assign wb_output.clz = new_request_r ? '0 : left_shift_amt;
    assign wb_output.subnormal = ~new_request_r & right_shift;
    assign wb_output.right_shift = ~new_request_r & right_shift;
    assign wb_output.right_shift_amt = right_shift_amt;
    assign wb_output.ignore_max_expo = new_request_r;

endmodule
