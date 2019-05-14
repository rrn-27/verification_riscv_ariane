`include "uvm_macros.svh"
package coverage;
import sequences::*;
import uvm_pkg::*;
import ariane_pkg::*;

class decoder_subscriber_in extends uvm_subscriber #(decoder_transaction_in);
    `uvm_component_utils(decoder_subscriber_in)

    //Declare Variables

    logic [63:0]        pc_i;                    
    logic               is_compressed_i;         
    logic [15:0]        compressed_instr_i;      
    logic               is_illegal_i;            
    logic [31:0]        instruction_i;           
    branchpredict_sbe_t branch_predict_i;
    exception_t         ex_i;                    
    riscv::priv_lvl_t   priv_lvl_i;              
    logic               debug_mode_i;            
    riscv::xs_t         fs_i;                    
    logic [2:0]         frm_i;                   
    logic               tvm_i;                   
    logic               tw_i;                    
    riscv::instruction_t instr_test;



    //TODO: Add covergroups for the inputs
    covergroup inputs;
    	opc_coverage: coverpoint instr_test.rtype.opcode {bins store = {7'b0100011};
			   			bins load = {7'b0000011};
						bins compare = {7'b1100011};
						bins reg_imm = {7'b0010011};
						bins atomic = {7'b0101111};
						bins reg_reg = {7'b0111011};
						bins int_reg = {7'b0110011};
						bins thirt_two_bit_int_reg ={7'b0011011};
						bins fmadd = {7'b1000011};
						bins fmsub = {7'b1000111};
						bins fnmsub = {7'b1001011};
						bins fnmadd = {7'b1001111};
						bins floating_mix = {7'b1010011};
						bins jalr = {7'b1100111};
						bins jal = {7'b1101111};
						bins auipc = {7'b0010111};
						bins lui = {7'b0110111};
			  		}
 	
	store_variants: coverpoint instr_test.stype.funct3 iff (instr_test.rtype.opcode == 7'b0100011) 
					{	bins sb = { 3'b000};
						bins sh = { 3'b001};
						bins sw = { 3'b010};
						bins sd = { 3'b011};
					}

	compare_variants: coverpoint instr_test.stype.funct3 iff (instr_test.rtype.opcode == 7'b1100011) 
				{		bins beq = { 3'b000};
						bins bne = { 3'b001};
						bins blt = { 3'b100};
						bins bge = { 3'b101};
						bins bltu = { 3'b110};
						bins bgeu = { 3'b111};}


	load_variants: coverpoint instr_test.itype.funct3 iff (instr_test.rtype.opcode == 7'b0000011) 
				{		bins lb = { 3'b000};
						bins lh = { 3'b001};
						bins lw = { 3'b010};
						bins ld = { 3'b011};
						bins lbu = { 3'b100};
						bins lhu = { 3'b101};
						bins lwu = { 3'b110}; }
//REVISIT - upper bits for SRL,SLL and SRA
	reg_imm_variants: coverpoint instr_test.itype.funct3 iff (instr_test.rtype.opcode == 7'b0010011) 
				{		bins add = { 3'b000};
						bins slt = { 3'b010};
						bins sltu = { 3'b011};
						bins xor_op = {3'b100};
						bins or_op = { 3'b110};
						bins and_op = { 3'b111};
						bins sll = { 3'b001};
						bins srl = { 3'b101};}
// REVISIT for 2
	atomic_coverage_f5: coverpoint instr_test.atype.funct5 iff (instr_test.atype.opcode == 7'b0101111)
					{	bins b9 = {5'h0};
						bins b10 = {5'h1};
						bins b11 = {5'h2};
						bins b12 = {5'h3};
						bins b13 = {5'h4};
						bins b14 = {5'h8};
						bins b15 = {5'hC};
						bins b16 = {5'h10};
						bins b17 = {5'h14};
						bins b18 = {5'h18};
						bins b19 = {5'h1C};

						}

	atomic_coverage_f3: coverpoint instr_test.atype.funct3 iff (instr_test.atype.opcode == 7'b0101111)
					{	bins word = {5'h2};
						bins double = {5'h3};
					}
				

	atomic_coverage: cross atomic_coverage_f5,atomic_coverage_f3;

	fp_store: coverpoint instr_test.stype.funct3 iff (instr_test.stype.opcode == 7'b0100111) 
					{	bins fsb = {3'b000};
						bins fsh = {3'b001};
						bins fsw = {3'b010};
						bins fsd = {3'b011};
					}
	fp_load: coverpoint instr_test.itype.funct3 iff (instr_test.itype.opcode == 7'b0000111) 
					{	bins flb = {3'b000};
						bins flh = {3'b001};
						bins flw = {3'b010};
						bins fld = {3'b011};
					}

	reg_imm_1: coverpoint {instr_test.rtype.funct7, instr_test.rtype.funct3}  iff (instr_test.itype.opcode == 7'b0111011) 
					{	
			     bins addw = {7'b0000000, 3'b000}; 
                             bins subw = {7'b0100000, 3'b000};
			     bins sllw = {7'b0000000, 3'b001};
                             bins srlw = {7'b0000000, 3'b101};
			     bins sraw = {7'b0100000, 3'b101};
                             bins mulw = {7'b0000001, 3'b000}; 
                             bins divw = {7'b0000001, 3'b100};
                             bins divuw = {7'b0000001, 3'b101};
			     bins remw = {7'b0000001, 3'b110};
			     bins remuw = {7'b0000001, 3'b111};}
	
	int_reg: coverpoint instr_test.rtype.funct3  iff ((instr_test.rvftype.funct2 != 2'b10) && (instr_test.itype.opcode ==7'b0110011))
		{
				bins add = {3'b000}; 
                                bins slts = {3'b010};
                                bins sltu = {3'b011};
                                bins xorl = {3'b100};
                                bins orl = {3'b110}; 
                                bins and_op = {3'b111};
                                bins sll = {3'b001}; 
                                bins srl = {3'b101}; 
		} 

	op_imm32: coverpoint instr_test.itype.funct3  iff (instr_test.itype.opcode ==7'b0011011)
		{
				bins addw = {3'b000}; 
                                bins sllw = {3'b001};
                               bins srlw_sraw = {3'b101};
		}

	fp_unit: coverpoint instr_test.rftype.funct5  iff (instr_test.itype.opcode ==7'b1010011)
		{
				bins fadd = {5'b00000}; 
				bins fsub = {5'b00001}; 
				bins fmul = {5'b00010}; 
				bins fdiv = {5'b00011}; 
				bins fsqrt = {5'b01011}; 
				bins fsgnj = {5'b00100}; 
				bins fmin_fmax = {5'b00101}; 
				bins fcvt = {5'b00101}; 
			}

    endgroup: inputs
    

    function new(string name, uvm_component parent);
        super.new(name,parent);
        // TODO: Uncomment
        inputs=new;
        
    endfunction: new

    function void write(decoder_transaction_in t);
       /* A={t.A};
        B={t.B};
        opcode={t.opcode};
        cin={t.CIN};*/

	pc_i=t.pc_i;              
	is_compressed_i=t.is_compressed_i;   
	compressed_instr_i=t.compressed_instr_i;
	is_illegal_i=t.is_illegal_i;      
	instruction_i=t.instruction_i;     
	branch_predict_i=t.branch_predict_i;
	ex_i=t.ex_i;              
	priv_lvl_i=t.priv_lvl_i;        
	debug_mode_i=t.debug_mode_i;      
	fs_i=t.fs_i;              
	frm_i=t.frm_i;             
	tvm_i=t.tvm_i;             
	tw_i=t.tw_i;              
    	instr_test = riscv::instruction_t'(instruction_i);

        // TODO: Uncomment
        inputs.sample();
        
    endfunction: write

endclass: decoder_subscriber_in

class decoder_subscriber_out extends uvm_subscriber #(decoder_transaction_out);
    `uvm_component_utils(decoder_subscriber_out)

    scoreboard_entry_t  instruction_o; 
    logic               is_control_flow_instr_o; 


    //TODO: Add covergroups for the outputs
    
    covergroup outputs;
	is_control_flow: coverpoint is_control_flow_instr_o { 	bins b1 = {1'b1};
			      				bins b2 = {1'b0};
			  			  }

	functional_units: coverpoint instruction_o.fu {	bins load = {LOAD};
			      				bins store = {STORE};
			      				bins alu = {ALU};
			      				bins cntrl_flow = {CTRL_FLOW};
			      				bins mult = {MULT};
			      				bins fpu = {FPU};
			      				//bins fpu_vec = {FPU_VEC};
			  			  }

	operator_coverage: coverpoint instruction_o.op {bins add = {ADD};
							bins sub = {SUB};
							bins addw =  {ADDW};
							bins subw = {SUBW};
							bins xorl =  {XORL};
							bins orl =  {ORL};
							bins andl = {ANDL};
							bins sra = {SRA};
							bins srl = {SRL};
							bins sll = {SLL};
							bins srlw = {SRLW};
							bins sllw = {SLLW};
							bins sraw =  {SRAW};
							bins lts = {LTS};
							bins ltu =  {LTU};
							bins ges = {GES};
							bins geu = {GEU};
							bins eq =  {EQ};
							bins ne =  {NE};
							bins jalr = {JALR};
							bins slts = {SLTS};
							bins sltu =  {SLTU};
							bins ld = {LD};
							bins sd=  {SD};
							bins lw =  {LW};
							bins lwu = {LWU};
							bins sw =  {SW};
							bins lh =  {LH};
							bins lhu = {LHU};
							bins sh = {SH};
							bins lb = {LB};
							bins sb = {SB};
							bins lbu = {LBU};
							bins amo_lrw = {AMO_LRW};
							bins amo_lrd = {AMO_LRD};
							bins amo_scw =  {AMO_SCW};
							bins amo_scd = {AMO_SCD};
				                        bins amo_swapw = {AMO_SWAPW};
							bins amo_addw = {AMO_ADDW};
							bins amo_andw =  {AMO_ANDW};
							bins amo_orw =  {AMO_ORW};
							bins amo_xorw =  {AMO_XORW};
							bins amo_maxw =  {AMO_MAXW};
							bins amo_maxwu= {AMO_MAXWU};
							bins amo_minw = {AMO_MINW};
							bins amo_minwu = {AMO_MINWU};
                               				bins amo_swapd = {AMO_SWAPD};
							bins amo_addd = {AMO_ADDD};
							bins amo_andd = {AMO_ANDD};
							bins amo_ord = {AMO_ORD};
							bins amo_xord = {AMO_XORD};
							bins amo_maxd = {AMO_MAXD};
							bins amo_maxdu={AMO_MAXDU};
							bins amo_mind = {AMO_MIND};
							bins amo_mindu={AMO_MINDU};
							bins mul = {MUL};
							bins mulh = {MULH};
							bins mulhu = {MULHU};
							bins mulhsu = {MULHSU};
							bins mulw = {MULW};
							bins div = {DIV};
							bins divu = {DIVU};
							bins divw = {DIVW};
							bins divuw= {DIVUW};
							bins rem= { REM};
							bins remu = {REMU};
							bins remw= {REMW};
							bins remuw={REMUW};
							bins fld = {FLD};
							bins flw ={FLW};
							bins flh = {FLH};
							bins flb = {FLB};
							bins fsd = {FSD};
							bins fsw= {FSW};
							bins fsh = {FSH};
							bins fsb = {FSB};
							bins fadd = {FADD};
							bins fsub = {FSUB};
							bins fmul = {FMUL};
							bins fdiv = {FDIV};
							bins fmin_max= {FMIN_MAX};
							bins fsqrt = {FSQRT};
							bins fmadd = {FMADD};
							bins fmsub = {FMSUB};
							bins fnmsub= {FNMSUB};
							bins fnmadd = {FNMADD};
							bins fcvt_f2i = {FCVT_F2I};
							bins fcvt_i2f={FCVT_I2F};
							bins fcvt_f2f={FCVT_F2F};
							bins fsgnj ={FSGNJ};
							bins fmv_f2x={FMV_F2X};
							bins fmv_x2f={FMV_X2F};
							bins fcmp = {FCMP};
							bins fclass = {FCLASS};
}
	exception_coverage : coverpoint instruction_o.ex.valid
				{
			bins zero = {0};
			bins one =  {1};
			}

	register_rd : coverpoint instruction_o.rd
				{
			bins reg_rd[] = {[0:31]};
		}
	
	register_rs1 : coverpoint instruction_o.rs1
                                {
			bins reg_rs1[] = {[0:31]};
                        }

	register_rs2 : coverpoint instruction_o.rs2
                                {
			bins reg_rs2[] = {[0:31]};
                        }

    endgroup: outputs
    

function new(string name, uvm_component parent);
    super.new(name,parent);
    // TODO: Uncomment
    outputs=new;
    
endfunction: new

function void write(decoder_transaction_out t);
    
    instruction_o = t.instruction_o;
    is_control_flow_instr_o = t.is_control_flow_instr_o;
    

    //TODO: Uncomment
    outputs.sample();

endfunction: write
endclass: decoder_subscriber_out

endpackage: coverage
