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

//to assume that the exception valid sinal is low so that no excceptions occur
assume_valid: assume property (@(posedge clk) (ex_i.valid == 0));

//to make the rs2 bits in the lrw and lrd instructions all 0
assume_lrw: assume property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b00010))|=>(instruction_o.rs2==5'b00000));
assume_lrd: assume property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b00010))|=>(instruction_o.rs2==5'b00000));

//to assume that the floating point valid signal is high to check the floating point instructions
assume_fs_valid: assume property (@(posedge clk) (fs_i !=riscv::Off));

//RS1 field = 0 constraint  for Privileged instructions
assume_sys_instr_1 : assume property (@(posedge clk) (opcode == 7'b1110011) && ((instr.itype.imm == 0) || (instr.itype.imm == 1) || (instr.itype.imm == 12'h2) || (instr.itype.imm == 12'h102) || (instr.itype.imm == 12'h105) || (instr.itype.imm == 12'h302)) |-> (instr.itype.rs1== 0));

//FUNCT3 field = 0 constraint  for Privileged instructions
assume_sys_instr_2 : assume property (@(posedge clk) (opcode == 7'b1110011)|-> (instr.itype.funct3== 0));
//RD field = 0 constraint  for Privileged instructions
assume_sys_instr_3 : assume property (@(posedge clk) (opcode == 7'b1110011)|-> (instr.itype.rd== 0));


//assertions	

//shvetha assertions

//assertreset: assert property (@(posedge reset_n) ((instruction_o.rs1==32'b0)&&(instruction_o.rs2==32'b0)&&(instruction_o.rd==32'b0)&&(instruction_o.op==ADD)&&(instruction_o.fu==NONE)));


//assertint_reg: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rvftype.funct2 != 2'b10))|=>((instruction_o.rs1==$past(instr.rtype.rs1))));
//assert_store: assert property (@(posedge clk) ((opcode==7'b0100011))|=>((instruction_o.use_imm==1)));
//assert_store_1: assert property (@(posedge clk) ((instr.stype.opcode==7'b0100011))|=>((instruction_o.rs1==$past(instr.stype.rs1))));

//&&(instruction_o.rs2==instr.rtype.rs2)&&(instruction_o.rd==instr.rtype.rd)));


//Control Flow Instructions
assertcontrol: assert property (@(posedge clk) ((opcode==7'b1100011)&&(instr.stype.funct3!=3'b010)&&(instr.stype.funct3!=3'b011)|=> ( is_control_flow_instr_o == 1'b1)));


//Integer Reg-Reg instructions
assertaluadd: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b000)&&(instr.rvftype.funct2 != 2'b10))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ADD)&&(instruction_o.fu==ALU)));

assertalusub: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0100000)&&(instr.rtype.funct3==3'b000)&&(instr.rvftype.funct2 != 2'b10))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SUB)&&(instruction_o.fu==ALU)));

assertalusll: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b001)&&(instr.rvftype.funct2 != 2'b10))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLL)&&(instruction_o.fu==ALU)));

assertaluslt: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b010))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLTS)&&(instruction_o.fu==ALU)));

assertalusltu: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b011))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLTU)&&(instruction_o.fu==ALU)));

assertaluxor: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==XORL)&&(instruction_o.fu==ALU)));

assertalusrl: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b101))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRL)&&(instruction_o.fu==ALU)));

assertalusra: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0100000)&&(instr.rtype.funct3==3'b101))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRA)&&(instruction_o.fu==ALU)));

assertaluor: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b110))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ORL)&&(instruction_o.fu==ALU)));

assertaluand: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b111))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ANDL)&&(instruction_o.fu==ALU)));

assertmul: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==MUL)&&(instruction_o.fu==MULT)));

assertmulh: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==MULH)&&(instruction_o.fu==MULT)));

assertmulhsu: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b010))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==MULHSU)&&(instruction_o.fu==MULT)));

assertmulhu: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b011))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==MULHU)&&(instruction_o.fu==MULT)));

assertdiv: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==DIV)&&(instruction_o.fu==MULT)));

assertdivu: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b101))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==DIVU)&&(instruction_o.fu==MULT)));

assertrem: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b110))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==REM)&&(instruction_o.fu==MULT)));

assertremu: assert property (@(posedge clk) ((opcode==7'b0110011)&&(instr.rtype.funct7==7'b0000001)&&(instr.rtype.funct3==3'b111))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==REMU)&&(instruction_o.fu==MULT)));


//32 bit Reg-Immediate Operations
assertaddiw: assert property (@(posedge clk) ((opcode==7'b0011011)&&(instr.rtype.funct3==3'b000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ADDW)&&(instruction_o.fu==ALU)));

assertslliw: assert property (@(posedge clk) ((opcode==7'b0011011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLLW)&&(instruction_o.fu==ALU)));

assertsrliw: assert property (@(posedge clk) ((opcode==7'b0011011)&&(instr.rtype.funct7==7'b0000000)&&(instr.rtype.funct3==3'b101))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRLW)&&(instruction_o.fu==ALU)));

assertsraiw: assert property (@(posedge clk) ((opcode==7'b0011011)&&(instr.rtype.funct7==7'b0100000)&&(instr.rtype.funct3==3'b101))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRAW)&&(instruction_o.fu==ALU)));


//LSU
assertsb: assert property (@(dge clk) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.op==SB)&&(instruction_o.fu==STORE)));

assertsh: assert property (@(posedge clk) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.op==SH)&&(instruction_o.fu==STORE)));

assertsw: assert property (@(posedge clk) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b010))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.op==SW)&&(instruction_o.fu==STORE)));

assertsd: assert property (@(posedge clk) ((opcode==7'b0100011)&&(instr.rtype.funct3==3'b011))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.op==SD)&&(instruction_o.fu==STORE)));

assertlb: assert property (@(posedge clk) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==LB)&&(instruction_o.fu==LOAD)));

assertlh: assert property (@(posedge clk) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==LH)&&(instruction_o.fu==LOAD)));

assertlw: assert property (@(posedge clk) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b010))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==LW)&&(instruction_o.fu==LOAD)));

assertlbu: assert property (@(posedge clk) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==LBU)&&(instruction_o.fu==LOAD)));

assertlhu: assert property (@(posedge clk) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b101))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==LHU)&&(instruction_o.fu==LOAD)));

assertlwu: assert property (@(posedge clk) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b110))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==LWU)&&(instruction_o.fu==LOAD)));

assertld: assert property (@(posedge clk) ((opcode==7'b0000011)&&(instr.rtype.funct3==3'b011))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==LD)&&(instruction_o.fu==LOAD)));


//32 bit Reg-Reg Operations
assertaddw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b000)&&(instr.rtype.funct7==7'b0000000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ADDW)&&(instruction_o.fu==ALU)));

assertsubw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b000)&&(instr.rtype.funct7==7'b0100000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SUBW)&&(instruction_o.fu==ALU)));

assertsllw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b001)&&(instr.rtype.funct7==7'b0000000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLLW)&&(instruction_o.fu==ALU)));

assertsrlw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b101)&&(instr.rtype.funct7==7'b0000000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRLW)&&(instruction_o.fu==ALU)));

assertsraw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b101)&&(instr.rtype.funct7==7'b0100000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRAW)&&(instruction_o.fu==ALU)));

assertmulw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b000)&&(instr.rtype.funct7==7'b0000001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==MULW)&&(instruction_o.fu==MULT)));

assertdivw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b100)&&(instr.rtype.funct7==7'b0000001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==DIVW)&&(instruction_o.fu==MULT)));

assertdivuw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b101)&&(instr.rtype.funct7==7'b0000001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==DIVUW)&&(instruction_o.fu==MULT)));

assertremw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b110)&&(instr.rtype.funct7==7'b0000001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==REMW)&&(instruction_o.fu==MULT)));

assertremuw: assert property (@(posedge clk) ((opcode==7'b0111011)&&(instr.rtype.funct3==3'b111)&&(instr.rtype.funct7==7'b0000001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rs2==$past(instr.rtype.rs2))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==REMUW)&&(instruction_o.fu==MULT)));


//Reg-Immediate Operations
assertaddi: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ADD)&&(instruction_o.fu==ALU)));

assertslti: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b010))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLTS)&&(instruction_o.fu==ALU)));

assertsltiu: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b011))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLTU)&&(instruction_o.fu==ALU)));

assertxori: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==XORL)&&(instruction_o.fu==ALU)));

assertori: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b110))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ORL)&&(instruction_o.fu==ALU)));

assertandi: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b111))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==ANDL)&&(instruction_o.fu==ALU)));

assertslli: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b001)&&(instr.rtype.funct7==7'b0000000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SLL)&&(instruction_o.fu==ALU)));

assertsrli: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b101)&&(instr.rtype.funct7==7'b0000000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRL)&&(instruction_o.fu==ALU)));

assertsrai: assert property (@(posedge clk) ((opcode==7'b0010011)&&(instr.rtype.funct3==3'b101)&&(instr.rtype.funct7==7'b0100000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==SRA)&&(instruction_o.fu==ALU)));


//Atomic Operations
assertlrw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b00010))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_LRW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==5'b00000)));

assertscw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b00011))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_SCW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoswapw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b00001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_SWAPW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoaddw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b00000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_ADDW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoxorw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b00100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_XORW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoandw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b01100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_ANDW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoorw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b01000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_ORW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamominw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b10000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MINW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamomaxw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b10100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MAXW)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamominuw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b11000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MINWU)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamomaxuw: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b010)&&(instr.instr[31:27]==5'b11100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MAXWU)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamolrd: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b00010))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_LRD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==5'b00000)));

assertamoscd: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b00011))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_SCD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoswapd: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b00001))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_SWAPD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoaddd: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b00000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_ADDD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoxord: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b00100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_XORD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoandd: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b01100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_ANDD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamoord: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b01000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_ORD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamomind: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b10000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MIND)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamomaxd: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b10100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MAXD)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamominud: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b11000))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MINDU)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));

assertamomaxud: assert property (@(posedge clk) ((opcode==7'b0101111)&&(instr.rtype.funct3==3'b011)&&(instr.instr[31:27]==5'b11100))|=>((instruction_o.rs1==$past(instr.rtype.rs1))&&(instruction_o.rd==$past(instr.rtype.rd))&&(instruction_o.op==AMO_MAXDU)&&(instruction_o.fu==STORE)&&(instruction_o.rs2==$past(instr.rtype.rs2))));


//Assertions for default
assertdefault: assert property (@(posedge clk) ((opcode==7'b0110011)||(opcode==7'b0111011)||(opcode==7'b0010011)||(opcode==7'b0011011)||(opcode==7'b0100011)||(opcode==7'b0000011)||(opcode==7'b0101111)) |=> ((instruction_o.pc == $past(pc_i))&&(instruction_o.trans_id==5'b0)&&(instruction_o.use_pc==1'b0)&&(instruction_o.is_compressed==$past(is_compressed_i))&&(instruction_o.use_zimm==1'b0)&&(instruction_o.bp==$past(branch_predict_i))));


//Sign extend Immediate instructions assertions
assertimm: assert property(@(posedge clk) ((opcode==7'b0010011)||(opcode==7'b0011011)||(opcode==7'b0000011))|=>((instruction_o.result ==  { {52 {$past(instruction_i[31])}}, $past(instruction_i[31:20]) })&&(instruction_o.use_imm)==1'b1));

assertsimm: assert property(@(posedge clk) ((opcode==7'b0100011))|=>((instruction_o.result == { {52 {$past(instruction_i[31])}}, $past(instruction_i[31:25]), $past(instruction_i[11:7]) })&&(instruction_o.use_imm==1'b1)));


//Floating point Reg Reg


assertfpregreg: assert property (@(posedge clk)((opcode==7'b1000011)||(opcode==7'b1000111)||(opcode==7'b1001011)||(opcode==7'b1001111))|=>((instruction_o.rs1 == $past(instr.r4type.rs1))&&(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.rd == $past(instr.r4type.rd))&&(instruction_o.fu == FPU)&&(!instruction_o.use_imm)&&(instruction_o.result == $past({59'b0, instr.r4type.rs3}))));
assertfpregreg1: assert property (@(posedge clk)(opcode==7'b1000011)|=>(instruction_o.op == FMADD));
assertfpregreg2: assert property (@(posedge clk)(opcode==7'b1000111)|=>(instruction_o.op == FMSUB));
assertfpregreg3: assert property (@(posedge clk)(opcode==7'b1001011)|=>(instruction_o.op == FNMSUB));
assertfpregreg4: assert property (@(posedge clk)(opcode==7'b1001111)|=>(instruction_o.op == FNMADD));

assertfpregreg5: assert property (@(posedge clk)((opcode==7'b1010011)|=>(instruction_o.rd == $past(instr.r4type.rd))&&(instruction_o.fu == FPU)));
assertfpregregfadd: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b00000)|=>(instruction_o.rs2 == $past(instr.r4type.rs1))&&(instruction_o.op == FADD)&&(instruction_o.rs1 == '0)&&!instruction_o.use_imm));

assertfpregregfsub: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b00001)|=>(instruction_o.rs2 == $past(instr.r4type.rs1))&&(instruction_o.op == FSUB)&&(instruction_o.rs1 == '0)&&!instruction_o.use_imm));
assertfpregregfmul: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b00010)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FMUL)&&(instruction_o.rs1 == $past(instr.r4type.rs1))));
assertfpregregfdiv: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b00011)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FDIV)&&(instruction_o.rs1 == $past(instr.r4type.rs1))));
assertfpregregfsqrt: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b01011)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FSQRT)&&(instruction_o.rs1 == $past(instr.r4type.rs1))));

assertfpregreg6: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b00100)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FSGNJ)&&(instruction_o.rs1 == $past(instr.r4type.rs1))));

assertfpregregminmax: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b00101)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FMIN_MAX)&&(instruction_o.rs1 == $past(instr.r4type.rs1))));
assertfpregreg7: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b01000)|=>(instruction_o.rs2 == $past(instr.r4type.rs1))&&(instruction_o.op == FCVT_F2F)&&(instruction_o.rs1 == $past(instr.r4type.rs1))&&instruction_o.use_imm&&(instruction_o.result==$past(i_imm(instruction_i)))));
assertfpregreg8: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b10100)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FCMP)&&(instruction_o.rs1 == $past(instr.r4type.rs1))));

assertfpregreg9: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b11000)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FCVT_F2I)&&(instruction_o.rs1 ==  $past(instr.r4type.rs1))&&instruction_o.use_imm&&(instruction_o.result==$past(i_imm(instruction_i)))));
assertfpregreg10: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b11010)|=>(instruction_o.rs2 == $past(instr.r4type.rs2))&&(instruction_o.op == FCVT_I2F)&&(instruction_o.rs1 ==  $past(instr.r4type.rs1))&&instruction_o.use_imm&&(instruction_o.result==$past(i_imm(instruction_i)))));

assertfpregreg11: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b11100)&&(instr.rftype.rm == 3'b000)|=>(instruction_o.rs2 == $past(instr.r4type.rs1))&&(instruction_o.op == FMV_F2X)&&(instruction_o.rs1 ==  $past(instr.r4type.rs1))));
assertfpregreg12: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b11100)&& XF16ALT && (instr.rftype.rm == 3'b100)|=>(instruction_o.rs2 == $past(instr.r4type.rs1))&&(instruction_o.op == FMV_F2X)&&(instruction_o.rs1 ==  $past(instr.r4type.rs1))));
assertfpregreg13: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b11100)&& ((instr.rftype.rm == 3'b001)||(XF16ALT && (instr.rftype.rm == 3'b101)))|=>(instruction_o.rs2 == $past(instr.r4type.rs1))&&(instruction_o.op == FCLASS)&&(instruction_o.rs1 ==  $past(instr.r4type.rs1))));
assertfpregreg14: assert property (@(posedge clk)((opcode==7'b1010011)&&(instr.rftype.funct5==5'b11110)|=>(instruction_o.rs2 == $past(instr.r4type.rs1))&&(instruction_o.op == FMV_X2F)&&(instruction_o.rs1 ==  $past(instr.r4type.rs1))));
//Assertions for Privileged instructions
assert_ecall: assert property (@(posedge clk) ((opcode==7'b1110011)&&(instr.itype.imm== 12'b0))|=>((instruction_o.rs1==0)&&(instruction_o.rd==0)&&(instruction_o.fu==CSR)));
assert_ebreak: assert property (@(posedge clk) ((opcode==7'b1110011)&&(instr.itype.imm== 12'b1))|=>((instruction_o.rs1==0)&&(instruction_o.rd==0)&&(instruction_o.fu==CSR)));
assert_uret: assert property (@(posedge clk) ((opcode==7'b1110011)&&(instr.itype.imm== 12'h2))|=>((instruction_o.rs1==0)&&(instruction_o.rd==0)&&(instruction_o.fu==CSR)));
assert_sret: assert property (@(posedge clk) ((opcode==7'b1110011)&&(instr.itype.imm== 12'h102))|=>((instruction_o.rs1==0)&&(instruction_o.rd==0)&&(instruction_o.fu==CSR)));
assert_mret: assert property (@(posedge clk) ((opcode==7'b1110011)&&(instr.itype.imm== 12'h302))|=>((instruction_o.rs1==0)&&(instruction_o.rd==0)&&(instruction_o.fu==CSR)));
assert_wfi: assert property (@(posedge clk) ((opcode==7'b1110011)&&(instr.itype.imm== 12'h105))|=>((instruction_o.rs1==0)&&(instruction_o.rd==0)&&(instruction_o.fu==CSR)));
assert_sfence: assert property (@(posedge clk) ((opcode==7'b1110011)&&(instr.itype.imm[31:25]== 12'h09))|=>((instruction_o.rs1==$past(instr.itype.rs1)&&(instruction_o.rd==$past(instr.itype.rd))&&(instruction_o.fu==CSR) && (instruction_o.rs2 == $past(instr.itype.imm[24:20])))));

//COVERS

cover_operand_rs1: cover property (@(posedge clk) instruction_o.rs1 == 5'd0);
cover_operand_rs2: cover property (@(posedge clk) instruction_o.rs2 == 5'd0);
cover_operand_rs1_1: cover property (@(posedge clk) instruction_o.rs1 == 5'b11111);
cover_operand_rs2_1: cover property (@(posedge clk) instruction_o.rs2 == 5'b11111);
cover_operand_rd1: cover property (@(posedge clk) instruction_o.rd == 5'd0);
cover_operand_rd1_1: cover property (@(posedge clk) instruction_o.rd == 5'b11111);







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

