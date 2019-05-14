
import ariane_pkg::*;
// Module for ALU verification
module alu_verif(
    input  logic                     clk_i,          
    input  logic                     rst_ni,         
    input  fu_data_t                 fu_data_i,
    input logic [63:0]              result_o,
    input logic                     alu_branch_res_o
);



logic equal;
logic less;
logic sless;
logic [63:0] inv;
logic [63:0] add;
logic [63:0] sub;
logic [63:0] sl;
logic [63:0] sr;
logic [63:0] sr_logical;
logic [31:0] slw;
logic [31:0] srw;
logic [31:0] srw_logical;
logic valid_operator;

assign equal = (fu_data_i.operand_a == fu_data_i.operand_b);
assign less = (fu_data_i.operand_a < fu_data_i.operand_b);
assign sless = ($signed(fu_data_i.operand_a) < $signed(fu_data_i.operand_b));
assign inv = ~fu_data_i.operand_b;

assign valid_operator = (fu_data_i.operator == EQ)||(fu_data_i.operator == NE)||(fu_data_i.operator == LTS)||(fu_data_i.operator == LTU)||(fu_data_i.operator == GEU)||(fu_data_i.operator == GES)||(fu_data_i.operator == SLTU) ||(fu_data_i.operator == SLTS)||(fu_data_i.operator == ANDL) ||(fu_data_i.operator ==ORL)||(fu_data_i.operator ==XORL)||(fu_data_i.operator == ADD)||(fu_data_i.operator == SUB)||(fu_data_i.operator == ADDW)||(fu_data_i.operator == SUBW)||(fu_data_i.operator == SRL)||(fu_data_i.operator == SLL)||(fu_data_i.operator == SRA)||(fu_data_i.operator == SLLW)||(fu_data_i.operator == SRLW)||(fu_data_i.operator == SRAW);


assign add = $signed(fu_data_i.operand_a) + $signed(fu_data_i.operand_b);
assign sub = fu_data_i.operand_a + inv + 64'd1;

assign sl = $signed(fu_data_i.operand_a)<< $signed(fu_data_i.operand_b[5:0]);
assign sr = $signed(fu_data_i.operand_a)>> $signed(fu_data_i.operand_b[5:0]);
assign sr_logical = $signed(fu_data_i.operand_a)>>> $signed(fu_data_i.operand_b[5:0]);

assign slw = $signed(fu_data_i.operand_a[31:0])<< $signed(fu_data_i.operand_b[4:0]);
assign srw = $signed(fu_data_i.operand_a[31:0])>> $signed(fu_data_i.operand_b[4:0]);
assign srw_logical = $signed(fu_data_i.operand_a[31:0])>>> $signed(fu_data_i.operand_b[4:0]);




// Write properties here


//ASSUMES


//Assume property to restrict the fu_data_i.operator to a valid value only

assume_prop_operator : assume property (@(posedge clk_i) disable iff(~rst_ni) valid_operator == 1);

//Assume property to restrict the values of operands to known values

assume_prop_a : assume property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operand_a !=64'dz)||(fu_data_i.operand_a !=64'dx));
assume_prop_b : assume property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operand_b !=64'dz)||(fu_data_i.operand_b !=64'dx));

//ASSERTS


//Reset


//Assert for reset condition for the outputs. Commented out because on debug found that the reset signal is not used within the source code and the
//outputs are invalidated in the issue stage at reset.


//assert_prop_check_reset : assert property (@(posedge clk_i) ($past(rst_ni==0))|-> $past((~alu_branch_res_o)&&(result_o==64'd0)));  

//Assert for Compare operations
//Checks for correct output in alu_branch_res_o for all branch operations


assert_prop_check_eq : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == EQ)  |-> (alu_branch_res_o==equal));  
assert_prop_check_neq : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == NE)  |-> (alu_branch_res_o==~equal));  
assert_prop_check_ltu : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == LTU) |-> (alu_branch_res_o==less));  
assert_prop_check_lts : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == LTS) |-> (alu_branch_res_o==sless));  
assert_prop_check_geu : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == GEU) |-> (alu_branch_res_o==~less));  
assert_prop_check_ges : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == GES) |-> (alu_branch_res_o==~sless));  

//Assert for Set compare operations
//Checks for correct output in result_o where the value of comparison is stored

assert_prop_check_slts : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SLTS) |-> (result_o == {63'b0, sless}));
assert_prop_check_sltu : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SLTU) |-> (result_o == {63'b0, less}));


//Assert for  Logic operation
//Checks for correct output for logic operation in result_o 

assert_prop_check_and : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == ANDL) |-> (result_o == (fu_data_i.operand_a & fu_data_i.operand_b)));  
assert_prop_check_or : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == ORL) |-> (result_o == (fu_data_i.operand_a | fu_data_i.operand_b)));  
assert_prop_check_xor : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == XORL) |-> (result_o == (fu_data_i.operand_a ^ fu_data_i.operand_b)));  


//Assert for Arithmetic operation
//Checks for correct output for arithmetic operations in result_o for 64bit and 32 bit(addw/subw)

assert_prop_check_add : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == ADD) |-> (result_o == add));
assert_prop_check_sub : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SUB) |-> (result_o == sub));
assert_prop_check_addw : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == ADDW) |-> (result_o == {{32{add[31]}},add[31:0]}));
assert_prop_check_subw : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SUBW) |-> (result_o == {{32{sub[31]}},sub[31:0]}));

//Assert for Shift operations
//Checks for correct output for shift operations in result_o for 64 bit and 32 bit(sllw/srlw/sraw)

assert_prop_check_sl : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SLL) |-> (result_o == sl));
assert_prop_check_sr : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SRL) |-> (result_o == sr));
assert_prop_check_sr_logical : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SRA) |-> (result_o == sr_logical));

assert_prop_check_slw : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SLLW) |-> (result_o == {{32{slw[31]}},slw}));
assert_prop_check_srw : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SRLW) |-> (result_o == {{32{srw[31]}},srw}));
assert_prop_check_srw_logical : assert property (@(posedge clk_i) disable iff(~rst_ni) (fu_data_i.operator == SRAW) |-> (result_o == {{32{srw_logical[31]}},srw_logical}));

//COVERS
//Cover properties to cover corner cases for inputs and outputs

cover_operand_a0: cover property (@(posedge clk_i) fu_data_i.operand_a == 64'd0);
cover_operand_b0: cover property (@(posedge clk_i) fu_data_i.operand_b == 64'd0);
cover_operand_a1: cover property (@(posedge clk_i) fu_data_i.operand_a == 64'hFFFFFFFFFFFFFFFF);
cover_operand_b1: cover property (@(posedge clk_i) fu_data_i.operand_b == 64'hFFFFFFFFFFFFFFFF);
cover_operand_sum1: cover property (@(posedge clk_i) result_o == 64'hFFFFFFFFFFFFFFFF);
cover_operand_sum0: cover property (@(posedge clk_i) result_o == 64'd0);
cover_operand_br1: cover property (@(posedge clk_i) alu_branch_res_o == 1'd1);
cover_operand_br0: cover property (@(posedge clk_i) alu_branch_res_o == 1'd0);



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
