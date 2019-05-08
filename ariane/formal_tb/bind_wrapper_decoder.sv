import ariane_pkg::*;

module decoder_props(
    input  logic [63:0]        pc_i,                    // PC from IF
    input  logic               is_compressed_i,         // is a compressed instruction
    input  logic [15:0]        compressed_instr_i,      // compressed form of instruction
    input  logic               is_illegal_i,            // illegal compressed instruction
    input  logic [31:0]        instruction_i,           // instruction from IF
    input  branchpredict_sbe_t branch_predict_i,
    input  exception_t         ex_i,                    // if an exception occured in if
    // From CSR
    input  riscv::priv_lvl_t   priv_lvl_i,              // current privilege level
    input  logic               debug_mode_i,            // we are in debug mode
    input  riscv::xs_t         fs_i,                    // floating point extension status
    input  logic [2:0]         frm_i,                   // floating-point dynamic rounding mode
    input  logic               tvm_i,                   // trap virtual memory
    input  logic               tw_i,                    // timeout wait
    input  logic               tsr_i,                   // trap sret
    input scoreboard_entry_t  instruction_o,           // scoreboard entry to scoreboard
    input logic               is_control_flow_instr_o, // this instruction will change the control flow
    //clk and reset
    input  logic               clk                     // clk added to the original design
//    input  logic               reset_n                  // reset added to the original design);
);

riscv::instruction_t instr;
assign instr = riscv::instruction_t'(instruction_i);

logic [6:0] opcode = instruction_i[6:0];

//assume
//assumereset: assume property (@(posedge reset_n) ((instruction_o.rs1==32'b0)&&(instruction_o.rs2==32'b0)&&(instruction_o.rd==32'b0)&&(instruction_o.op==ADD)&&(instruction_o.fu==NONE)));


//assertions	

//shvetha assertions

//assertreset: assert property (@(posedge reset_n) ((instruction_o.rs1==32'b0)&&(instruction_o.rs2==32'b0)&&(instruction_o.rd==32'b0)&&(instruction_o.op==ADD)&&(instruction_o.fu==NONE)));

assertaluadd: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b000))|=>((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==ADD)&&(instruction_o.fu==ALU)));

/*assertalusub: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0100000)&&(instr.rtype.funct3==3'b000))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SUB)&&(instruction_o.fu==ALU)));

assertalusll: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b001))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SLL)&&(instruction_o.fu==ALU)));

assertaluslt: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b010))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SLTS)&&(instruction_o.fu==ALU)));

assertalusltu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b011))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SLTU)&&(instruction_o.fu==ALU)));

assertaluxor: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b100))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==XORL)&&(instruction_o.fu==ALU)));

assertalusrl: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b101))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SRL)&&(instruction_o.fu==ALU)));

assertalusra: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0100000)&&(instr.rtype.funct3==3'b101))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SRA)&&(instruction_o.fu==ALU)));

assertaluor: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b110))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==ORL)&&(instruction_o.fu==ALU)));

assertaluand: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b111))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==ANDL)&&(instruction_o.fu==ALU)));

assertmul: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b000))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==MUL)&&(instruction_o.fu==MULT)));

assertmulh: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b001))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==MULH)&&(instruction_o.fu==MULT)));

assertmulhsu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b010))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==MULHSU)&&(instruction_o.fu==MULT)));

assertmulhu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b011))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==MULHU)&&(instruction_o.fu==MULT)));

assertdiv: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b100))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==DIV)&&(instruction_o.fu==MULT)));

assertdivu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b101))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==DIVU)&&(instruction_o.fu==MULT)));

assertrem: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b110))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==REM)&&(instruction_o.fu==MULT)));

assertremu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b111))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==REMU)&&(instruction_o.fu==MULT)));

assertaddiw: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0011011)&&(instr.rtype.funct3==3'b000))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==ADDW)&&(instruction_o.fu==ALU)));

assertslliw: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b001))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SLLW)&&(instruction_o.fu==ALU)));

assertsrliw: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b101))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SRLW)&&(instruction_o.fu==ALU)));

assertsraiw: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0100000)&&(instr.rtype.funct3==3'b101))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==SRAW)&&(instruction_o.fu==ALU)));

assertsb: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b000))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.op==SB)&&(instruction_o.fu==STORE)));

assertsh: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b001))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.op==SH)&&(instruction_o.fu==STORE)));

assertsw: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b010))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.op==SW)&&(instruction_o.fu==STORE)));

assertsd: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b011))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.op==SD)&&(instruction_o.fu==STORE)));

assertlb: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b000))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==LB)&&(instruction_o.fu==LOAD)));

assertlh: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b001))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==LH)&&(instruction_o.fu==LOAD)));

assertlw: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b010))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==LW)&&(instruction_o.fu==LOAD)));

assertlbu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b100))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==LBU)&&(instruction_o.fu==LOAD)));

assertlhu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b101))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==LHU)&&(instruction_o.fu==LOAD)));

assertlwu: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b110))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==LWU)&&(instruction_o.fu==LOAD)));

assertld: assert property (@(posedge clk) disable iff(~reset_n) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b011))|->((instruction_o.rs1==instr.rtype.rs1)&&(instruction_o.rd==instr.rtype.rd)&&(instruction_o.op==LD)&&(instruction_o.fu==LOAD)));

*/

endmodule

module Wrapper;

bind decoder decoder_props
decoder_tb_inst(
.pc_i(pc_i),                    
.is_compressed_i(is_compressed_i),         
.compressed_instr_i(compressed_instr_i),      
.is_illegal_i(is_illegal_i),            
.instruction_i(instruction_i),           
.branch_predict_i(branch_predict_i),
.ex_i(ex_i),                    
.priv_lvl_i(priv_lvl_i),              
.debug_mode_i(debug_mode_i),            
.fs_i(fs_i),                    
.frm_i(frm_i),                   
.tvm_i(tvm_i),                   
.tw_i(tw_i),                    
.tsr_i(tsr_i),                   
.instruction_o(instruction_o),           
.is_control_flow_instr_o(is_control_flow_instr_o),
.clk(clk)                     
//.reset_n(reset_n)                  

);

endmodule

