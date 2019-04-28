
import ariane_pkg::*;
// Module for ALU verification
module alu_verif(
    input  logic                     clk_i,          
    input  logic                     rst_ni,         
    input  fu_data_t                 fu_data_i,
    input logic [63:0]              result_o,
    input logic                     alu_branch_res_o
);


// Write properties here

assert_prop_check_eq : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == EQ) && ((fu_data_i.operand_a) == (fu_data_i.operand_b)) |-> alu_branch_res_o);  

endmodule

module Wrapper;

bind alu alu_verif
alu_tb_inst(
.clk_i(clk_i),
.rst_ni(rst_ni),
.fu_data_i(fu_data_i),
.result_o(result_o),
.alu_branch_res_o(alu_branch_res_o)
);

endmodule
