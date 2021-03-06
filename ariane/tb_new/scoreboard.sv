`include "uvm_macros.svh"
package scoreboard; 
import uvm_pkg::*;
import sequences::*;
import ariane_pkg::*;

class decoder_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(decoder_scoreboard)

    uvm_analysis_export #(decoder_transaction_in) sb_in;
    uvm_analysis_export #(decoder_transaction_out) sb_out;

    uvm_tlm_analysis_fifo #(decoder_transaction_in) fifo_in;
    uvm_tlm_analysis_fifo #(decoder_transaction_out) fifo_out;

    decoder_transaction_in tx_in;
    decoder_transaction_out tx_out;

    function new(string name, uvm_component parent);
        super.new(name,parent);
        tx_in=new("tx_in");
        tx_out=new("tx_out");
    endfunction: new

    function void build_phase(uvm_phase phase);
        sb_in=new("sb_in",this);
        sb_out=new("sb_out",this);
        fifo_in=new("fifo_in",this);
        fifo_out=new("fifo_out",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        sb_in.connect(fifo_in.analysis_export);
        sb_out.connect(fifo_out.analysis_export);
    endfunction: connect_phase

    task run();
        forever begin
            fifo_in.get(tx_in);
            fifo_out.get(tx_out);
            compare();
        end
    endtask: run

    extern virtual function scoreboard_entry_t getresult_scoreboard_entry; 
    extern virtual function logic getresult_cntrl_flow; 
    extern virtual function void compare;
        
endclass: decoder_scoreboard

function void decoder_scoreboard::compare;
    //TODO: Write this function to check whether the output of the DUT matches
    //the spec.
    //Use the getresult() function to get the spec output.
    //Consider using `uvm_info(ID,MSG,VERBOSITY) in this function to print the
    //results of the comparison.
    //You can use tx_in.convert2string() and tx_out.convert2string() for
    //debugging purposes

    scoreboard_entry_t instr_check;
    scoreboard_entry_t instr_output;
    logic tb_is_control_flow;
    logic rtl_is_control;
    instr_check = getresult_scoreboard_entry();
    instr_output = tx_out.instruction_o;
	
	tb_is_control_flow = getresult_cntrl_flow();
	rtl_is_control = tx_out.is_control_flow_instr_o;
         

    if(instr_check.pc != instr_output.pc) begin
	`uvm_info("Compare_failed",$sformatf("Expected PC = %b Got PC = %b",instr_check.pc,instr_output.pc),UVM_LOW);
    end
    else if(instr_check.fu != instr_output.fu) begin
	`uvm_info("Compare_failed",$sformatf("Expected FU= %s Got FU = %s",instr_check.fu,instr_output.fu),UVM_LOW);
    end
    else if(instr_check.op != instr_output.op) begin
	`uvm_info("Compare_failed",$sformatf("Expected OP = %b Got OP = %b",instr_check.op,instr_output.op),UVM_LOW);
    end
    else if(instr_check.rs1 != instr_output.rs1) begin
	`uvm_info("Compare_failed",$sformatf("Expected RS1 = %b Got RS1 = %b",instr_check.rs1,instr_output.rs1),UVM_LOW);
    end
    else if(instr_check.rs2 != instr_output.rs2) begin
	`uvm_info("Compare_failed",$sformatf("Expected RS2 = %b Got RS2 = %b",instr_check.rs2,instr_output.rs2),UVM_LOW);
    end
    else if(instr_check.rd != instr_output.rd) begin
	`uvm_info("Compare_failed",$sformatf("Expected RD = %b Got RD = %b",instr_check.rd,instr_output.rd),UVM_LOW);
    end
    else if(instr_check.result != instr_output.result) begin
	`uvm_info("Compare_failed",$sformatf("Expected Result = %b Got Result = %b",instr_check.result,instr_output.result),UVM_LOW);
    end
    else if(instr_check.valid != instr_output.valid) begin
	`uvm_info("Compare_failed",$sformatf("Expected Valid = %b Got Valid = %b",instr_check.valid,instr_output.valid),UVM_LOW);
    end
    else if(instr_check.use_imm != instr_output.use_imm) begin
	`uvm_info("Compare_failed",$sformatf("Expected Use Imm = %b Got Use Imm = %b",instr_check.use_imm,instr_output.use_imm),UVM_LOW);
    end
    else if(instr_check.use_pc != instr_output.use_pc) begin
	`uvm_info("Compare_failed",$sformatf("Expected Use PC = %b Got Use PC = %b",instr_check.use_pc,instr_output.use_pc),UVM_LOW);
    end
    else if(instr_check.bp != instr_output.bp) begin
	`uvm_info("Compare_failed",$sformatf("Expected BP = %b Got BP = %b",instr_check.bp,instr_output.bp),UVM_LOW);
    end
    else if(instr_check.is_compressed != instr_output.is_compressed) begin
	`uvm_info("Compare_failed",$sformatf("Expected Is compressed = %b Got Is compressed = %b",instr_check.is_compressed,instr_output.is_compressed),UVM_LOW);
    end
    else if(instr_check.ex != instr_output.ex) begin
	`uvm_info("Compare_failed",$sformatf("Exception expected = %b Got exception = %b",instr_check.ex.valid,instr_output.ex.valid),UVM_LOW);
    end
    else if(rtl_is_control != tb_is_control_flow) begin
	`uvm_info("Compare_failed",$sformatf("Control flow expected = %b Got control flow = %b",tb_is_control_flow,rtl_is_control),UVM_LOW);
    end
    else begin
//	`uvm_info("Compare_success","Decoder output equal",UVM_LOW);
//	`uvm_info("Compare_success",$sformatf("Expected = %b Got = %b",instr_check.pc,instr_output.pc),UVM_LOW);
//	`uvm_info("Compare_success",$sformatf("Expected = %b Got = %b",instr_check.fu,instr_output.fu),UVM_LOW);
    end

endfunction

function scoreboard_entry_t decoder_scoreboard::getresult_scoreboard_entry;
    //TODO: Remove the statement below
    //Modify this function to return a 34-bit result {VOUT, COUT,OUT[31:0]} which is
    //consistent with the given spec.

    logic           	clk, reset_n;
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
    logic illegal_instr; 
    logic ecall;
    logic ebreak;              
    logic check_fprm;              
    riscv::instruction_t instr_test;
    scoreboard_entry_t collect_instr_o;

    pc_i = tx_in.pc_i;
    is_compressed_i = tx_in.is_compressed_i;
    is_illegal_i = tx_in.is_illegal_i;
    instruction_i = tx_in.instruction_i;
    branch_predict_i = tx_in.branch_predict_i;
    ex_i = tx_in.ex_i;
    priv_lvl_i = tx_in.priv_lvl_i;
    debug_mode_i = tx_in.debug_mode_i;
    fs_i = tx_in.fs_i;
    frm_i = tx_in.frm_i;
    tvm_i = tx_in.tvm_i;
    tw_i = tx_in.tw_i;
    ecall = 0;
    ebreak = 0;

    instr_test = riscv::instruction_t'(instruction_i);
  // `uvm_info("Scoreboard",$sformatf("Opcode = %b",instruction_i[6:0]),UVM_LOW);
   
	
        collect_instr_o.result        = 64'b0;
        collect_instr_o.use_imm        = 1'b0;
        illegal_instr               = 1'b0;
        collect_instr_o.pc            = pc_i;
        collect_instr_o.trans_id      = 5'b0;
        collect_instr_o.fu            = NONE;
        collect_instr_o.op            = ADD;
        collect_instr_o.rs1           = '0;
        collect_instr_o.rs2           = '0;
        collect_instr_o.rd            = '0;
        collect_instr_o.use_pc        = 1'b0;
        collect_instr_o.trans_id      = '0;
        collect_instr_o.is_compressed = is_compressed_i;
        collect_instr_o.use_zimm      = 1'b0;
        collect_instr_o.bp            = branch_predict_i;
        ecall                       = 1'b0;
        ebreak                      = 1'b0;
        check_fprm                  = 1'b0;

        if (~ex_i.valid) begin
//---------------------------------------
	// Integer Store
//---------------------------------------
            case (instr_test.rtype.opcode)
               7'b0100011: begin
                    collect_instr_o.fu  = STORE;
                    collect_instr_o.use_imm = 1 ;
                    collect_instr_o.result = {{52 {instruction_i[31]}}, instruction_i[31:25], instruction_i[11:7]};
                    collect_instr_o.rs1[4:0]  = instr_test.stype.rs1;
                    collect_instr_o.rs2[4:0]  = instr_test.stype.rs2;
                    case (instr_test.stype.funct3)
                        3'b000: collect_instr_o.op  = SB;
                        3'b001: collect_instr_o.op  = SH;
                        3'b010: collect_instr_o.op  = SW;
                        3'b011: collect_instr_o.op  = SD;
                        default: illegal_instr = 1'b1;
                    endcase
                end
//---------------------------------------
		//Integer LOAD
//---------------------------------------
                7'b0000011: begin
                    collect_instr_o.fu  = LOAD;
               	    collect_instr_o.result =  {{52 {instruction_i[31]}}, instruction_i[31:20]};
                    collect_instr_o.use_imm = 1'b1;
                    collect_instr_o.rs1[4:0] = instr_test.itype.rs1;
                    collect_instr_o.rd[4:0]  = instr_test.itype.rd;
                   case (instr_test.itype.funct3)
                        3'b000: collect_instr_o.op  = LB;
                        3'b001: collect_instr_o.op  = LH;
                        3'b010: collect_instr_o.op  = LW;
                        3'b100: collect_instr_o.op  = LBU;
                        3'b101: collect_instr_o.op  = LHU;
                        3'b110: collect_instr_o.op  = LWU;
                        3'b011: collect_instr_o.op  = LD;
                        default: illegal_instr = 1'b1;
                    endcase
                end


//---------------------------------------
// Floating Point Store
//---------------------------------------
                7'b0100111: begin
                    if (FP_PRESENT && fs_i != riscv::Off) begin 
                        collect_instr_o.fu  = STORE;
                        collect_instr_o.result = {{52 {instruction_i[31]}}, instruction_i[31:25], instruction_i[11:7]};
                        collect_instr_o.use_imm = 1'b1;
                        collect_instr_o.rs1        = instr_test.stype.rs1;
                        collect_instr_o.rs2        = instr_test.stype.rs2;
                        // determine store size
                        case (instr_test.stype.funct3)
                            // Only process instruction if corresponding extension is active (static)
                            3'b000: if (XF8) collect_instr_o.op = FSB;
                                    else illegal_instr = 1'b1;
                            3'b001: if (XF16 | XF16ALT) collect_instr_o.op = FSH;
                                    else illegal_instr = 1'b1;
                            3'b010: if (RVF) collect_instr_o.op = FSW;
                                    else illegal_instr = 1'b1;
                            3'b011: if (RVD) collect_instr_o.op = FSD;
                                    else illegal_instr = 1'b1;
                            default: illegal_instr = 1'b1;
                        endcase
                    end else
                        illegal_instr = 1'b1;
                end

//---------------------------------------
// Floating Point Load
//---------------------------------------
                7'b0000111: begin
                    if (FP_PRESENT && fs_i != riscv::Off) begin 
                        collect_instr_o.fu  = LOAD;
               	        collect_instr_o.result =  {{52 {instruction_i[31]}}, instruction_i[31:20]};
                        collect_instr_o.use_imm = 1'b1;
                        collect_instr_o.rs1       = instr_test.itype.rs1;
                        collect_instr_o.rd        = instr_test.itype.rd;
                        case (instr_test.itype.funct3)
                            3'b000: if (XF8) collect_instr_o.op = FLB;
                                    else illegal_instr = 1'b1;
                            3'b001: if (XF16 | XF16ALT) collect_instr_o.op = FLH;
                                    else illegal_instr = 1'b1;
                            3'b010: if (RVF) collect_instr_o.op  = FLW;
                                    else illegal_instr = 1'b1;
                            3'b011: if (RVD) collect_instr_o.op  = FLD;
                                    else illegal_instr = 1'b1;
                            default: illegal_instr = 1'b1;
                        endcase
                    end else
                        illegal_instr = 1'b1;
                end

//---------------------------------------
// Register Immidiate operations
//---------------------------------------
                7'b0010011: begin
                    collect_instr_o.fu  = ALU;
               	    collect_instr_o.result =  {{52 {instruction_i[31]}}, instruction_i[31:20]};
                    collect_instr_o.use_imm = 1'b1;
                    collect_instr_o.rs1[4:0] = instr_test.itype.rs1;
                    collect_instr_o.rd[4:0]  = instr_test.itype.rd;

                    case (instr_test.itype.funct3)
                        3'b000: collect_instr_o.op = ADD;  
                        3'b010: collect_instr_o.op = SLTS; 
                        3'b011: collect_instr_o.op = SLTU; 
                        3'b100: collect_instr_o.op = XORL; 
                        3'b110: collect_instr_o.op = ORL;   
                        3'b111: collect_instr_o.op = ANDL;  

                        3'b001: begin
                          collect_instr_o.op = SLL;  // Shift Left Logical
                          if (instr_test.instr[31:26] != 6'b0)
                            illegal_instr = 1'b1;
                        end

                        3'b101: begin
                            if (instr_test.instr[31:26] == 6'b0)
                                collect_instr_o.op = SRL;  // Shift Right Logical
                            else if (instr_test.instr[31:26] == 6'b010_000)
                                collect_instr_o.op = SRA;  // Shift Right Arithmetic
                            else
                                illegal_instr = 1'b1;
                        end
                    endcase
                end

//---------------------------------------------------------------------------
//			32 BIT REG - REG				   //
//---------------------------------------------------------------------------


        	7'b0111011: begin
        		collect_instr_o.fu  = (instr_test.rtype.funct7 == 7'd1) ? MULT : ALU;
        	        collect_instr_o.rs1[4:0] = instr_test.rtype.rs1;
        	        collect_instr_o.rs2[4:0] = instr_test.rtype.rs2;
        	        collect_instr_o.rd[4:0]  = instr_test.rtype.rd;

        	        case ({instr_test.rtype.funct7, instr_test.rtype.funct3})
        	             {7'b0000000, 3'b000}: collect_instr_o.op = ADDW; // addw
        	             {7'b0100000, 3'b000}: collect_instr_o.op = SUBW; // subw
        	             {7'b0000000, 3'b001}: collect_instr_o.op = SLLW; // sllw
        	             {7'b0000000, 3'b101}: collect_instr_o.op = SRLW; // srlw
        	             {7'b0100000, 3'b101}: collect_instr_o.op = SRAW; // sraw
        	             // Multiplications
        	             {7'b0000001, 3'b000}: collect_instr_o.op = MULW;
        	             {7'b0000001, 3'b100}: collect_instr_o.op = DIVW;
        	             {7'b0000001, 3'b101}: collect_instr_o.op = DIVUW;
        	             {7'b0000001, 3'b110}: collect_instr_o.op = REMW;
        	             {7'b0000001, 3'b111}: collect_instr_o.op = REMUW;
        	             default: illegal_instr = 1'b1;
        	        endcase
        	end


////////////////////////////////////////////////////////////////////////////

///////////		ATOMIC OPERATIONS			////////////

////////////////////////////////////////////////////////////////////////////



		7'b0101111: begin		
			collect_instr_o.fu = STORE;		
			collect_instr_o.rs1[4:0] = instr_test.atype.rs1;
			collect_instr_o.rs2[4:0] = instr_test.atype.rs2;
			collect_instr_o.rd[4:0] = instr_test.atype.rd;

			case (instr_test.stype.funct3)
				3'h2: begin
				    case (instr_test.instr[31:27])
        	                    	5'h0:  collect_instr_o.op = AMO_ADDW;
        	                    	5'h1:  collect_instr_o.op = AMO_SWAPW;
        	                    	5'h2:  begin 
					       collect_instr_o.op = AMO_LRW;
        	                               if (instr_test.atype.rs2 != 0) illegal_instr = 1'b1;
					end
        	                    	5'h3:  collect_instr_o.op = AMO_SCW;
        	                    	5'h4:  collect_instr_o.op = AMO_XORW;
        	                    	5'h8:  collect_instr_o.op = AMO_ORW;
        	                    	5'hC:  collect_instr_o.op = AMO_ANDW;
        	                    	5'h10: collect_instr_o.op = AMO_MINW;
        	                    	5'h14: collect_instr_o.op = AMO_MAXW;
        	                    	5'h18: collect_instr_o.op = AMO_MINWU;
        	                    	5'h1C: collect_instr_o.op = AMO_MAXWU;
        	                    	default: illegal_instr = 1'b1;
				    endcase
				end
				3'h3: begin
				    case (instr_test.instr[31:27])
        	                        5'h0:  collect_instr_o.op = AMO_ADDD;
        	                        5'h1:  collect_instr_o.op = AMO_SWAPD;
        	                        5'h2:  begin
					       collect_instr_o.op = AMO_LRD;
        	                               if (instr_test.atype.rs2 != 0) illegal_instr = 1'b1;
					end
        	                        5'h3:  collect_instr_o.op = AMO_SCD;
        	                        5'h4:  collect_instr_o.op = AMO_XORD;
        	                        5'h8:  collect_instr_o.op = AMO_ORD;
        	                        5'hC:  collect_instr_o.op = AMO_ANDD;
        	                        5'h10: collect_instr_o.op = AMO_MIND;
        	                        5'h14: collect_instr_o.op = AMO_MAXD;
        	                        5'h18: collect_instr_o.op = AMO_MINDU;
        	                        5'h1C: collect_instr_o.op = AMO_MAXDU;
        	                    	default: illegal_instr = 1'b1;
        	                    endcase
				 end
        	                 default: illegal_instr = 1'b1;			
			endcase
		    

		end
		
////////////////////////////////////////////////////////////////////////////

///////////			CONTROL FLOW			////////////

////////////////////////////////////////////////////////////////////////////


		7'b1100011: begin		//Compare
			collect_instr_o.fu = CTRL_FLOW;		//Control flow
			collect_instr_o.rs1[4:0] = instr_test.stype.rs1;
			collect_instr_o.rs2[4:0] = instr_test.stype.rs2;
	//		control_flow = 1'd1;
        	        collect_instr_o.result = sb_imm(tx_in.instruction_i);
        	        collect_instr_o.use_imm = 1'b1;

			case(instr_test.stype.funct3)
				3'b000:collect_instr_o.op = EQ;
				3'b001:collect_instr_o.op = NE;
				3'b100:collect_instr_o.op = LTS;
				3'b110:collect_instr_o.op = LTU;
				3'b101:collect_instr_o.op = GES;  
				3'b111:collect_instr_o.op = GEU;
 				default: begin
        //	                    control_flow = 1'b0;
        	                    illegal_instr = 1'b1;
        	                end
				
			endcase
		end

		7'b1100111: begin		//JALR
			collect_instr_o.fu = CTRL_FLOW;
			collect_instr_o.rs1[4:0] 	= instr_test.itype.rs1;
			collect_instr_o.rd[4:0]   	= instr_test.itype.rd;
	//		control_flow 	= 1'd1;
        	        collect_instr_o.result 	= i_imm(tx_in.instruction_i);
        	        collect_instr_o.use_imm 	= 1'b1;
			case(instr_test.stype.funct3)
				3'b000:collect_instr_o.op = JALR;
				default: begin
        	          //          control_flow = 1'b0;  
        	                    illegal_instr = 1'b1;
        	                end

			endcase
		end

		7'b1101111: begin		//JAL
			collect_instr_o.fu = CTRL_FLOW;
			collect_instr_o.rd[4:0]   	= instr_test.itype.rd;
	//		control_flow 	= 1'd1;
        	        collect_instr_o.result 	= uj_imm(tx_in.instruction_i);
        	        collect_instr_o.use_imm 	= 1'b1;
		end

		7'b0010111: begin		//AUIPC
			collect_instr_o.fu = ALU;
			collect_instr_o.rd[4:0]   	= instr_test.itype.rd;
        	        collect_instr_o.result 	= { {32 {tx_in.instruction_i[31]}}, tx_in.instruction_i[31:12], 12'b0 };
        	        collect_instr_o.use_imm 	= 1'b1;
			collect_instr_o.use_pc 	= 1'b1;
			
		end
		7'b0110111: begin		//LUI
			collect_instr_o.fu = ALU;
			collect_instr_o.rd[4:0]   	= instr_test.itype.rd;
        	        collect_instr_o.result 	= { {32 {tx_in.instruction_i[31]}}, tx_in.instruction_i[31:12], 12'b0 };
        	        collect_instr_o.use_imm 	= 1'b1;
		end

// ----------------------------------
// Floating-Point Reg-Reg Operations
// ----------------------------------
		7'b1000011, 7'b1000111, 7'b1001011, 7'b1001111 : begin
        		if (tx_in.fs_i != riscv::Off) begin 
        	                collect_instr_o.fu  = FPU;
        	                collect_instr_o.rs1 = instr_test.r4type.rs1;
        	                collect_instr_o.rs2 = instr_test.r4type.rs2;
        	                collect_instr_o.rd  = instr_test.r4type.rd;
        	          	collect_instr_o.result = {59'b0, instr_test.r4type.rs3};
        	        	collect_instr_o.use_imm = 1'b0;
        	                check_fprm        = 1'b1;
        	                case (instr_test.r4type.opcode)
        	                    default:      collect_instr_o.op = FMADD;  
        	                    7'b1000111:   collect_instr_o.op = FMSUB;  
        	                    7'b1001011:   collect_instr_o.op = FNMSUB; 
        	                    7'b1001111:   collect_instr_o.op = FNMADD;
        	                endcase

        	                case (instr_test.r4type.funct2)
        	                    2'b00: if (~RVF)             illegal_instr = 1'b1;
        	                    2'b01: if (~RVD)             illegal_instr = 1'b1;
        	                    2'b10: if (~XF16 & ~XF16ALT) illegal_instr = 1'b1;
        	                    2'b11: if (~XF8)             illegal_instr = 1'b1;
        	                    default: illegal_instr = 1'b1;
        	                endcase


        	                case (instr_test.rftype.rm) inside
        	                    [3'b000:3'b100]: ; 
        	                    3'b101: begin      //extra rounding mode specific to ariane
        	                        if (~XF16ALT || instr_test.rftype.fmt != 2'b10)
        	                            illegal_instr = 1'b1;
        	                        case (tx_in.frm_i) inside 
        	                            [3'b000:3'b100]: ; 
        	                            default : illegal_instr = 1'b1;
        	                        endcase
        	                    end
        	                    3'b111: begin	//extra rounding mode specific to ariane
        	                        case (tx_in.frm_i) inside
        	                            [3'b000:3'b100]: ; 
        	                            default : illegal_instr = 1'b1;
        	                        endcase
        	                    end
        	                    default : illegal_instr = 1'b1;
        	                endcase
			end else begin
				illegal_instr = 1'b1;
        	        end
		end
//----------------------
// Floating point instructions
//----------------------

		7'b1010011 : begin
        		if (tx_in.fs_i != riscv::Off) begin 
        	                collect_instr_o.fu  = FPU;
        	                collect_instr_o.rs1 = instr_test.rftype.rs1;
        	                collect_instr_o.rs2 = instr_test.rftype.rs2;
        	                collect_instr_o.rd  = instr_test.rftype.rd;
        	                check_fprm        = 1'b1;
        	                case (instr_test.rftype.funct5)
        	                    5'b00000: begin
        	                        collect_instr_o.op  = FADD;           
        	                        collect_instr_o.rs1 = '0;             
        	                        collect_instr_o.rs2 = instr_test.rftype.rs1;
        	        		collect_instr_o.result = i_imm(tx_in.instruction_i);
        	                    end
        	                    5'b00001: begin
        	                        collect_instr_o.op  = FSUB;  
        	                        collect_instr_o.rs1 = '0;    
        	                        collect_instr_o.rs2 = instr_test.rftype.rs1; 
        	               		collect_instr_o.result = i_imm(tx_in.instruction_i);
        	                    end
        	                    5'b00010: collect_instr_o.op = FMUL;  
        	                    5'b00011: collect_instr_o.op = FDIV; 
        	                    5'b01011: begin
        	                        collect_instr_o.op = FSQRT; 
        	                        if (instr_test.rftype.rs2 != 5'b00000) illegal_instr = 1'b1;
        	                    end
        	                    5'b00100: begin
        	                        collect_instr_o.op = FSGNJ; 
        	                        check_fprm       = 1'b0;  
        	                        if (XF16ALT) begin        
        	                            if (!(instr_test.rftype.rm inside {[3'b000:3'b010], [3'b100:3'b110]})) 
        	                                illegal_instr = 1'b1;
        	                        end else begin
        	                            if (!(instr_test.rftype.rm inside {[3'b000:3'b010]}))
        	                                illegal_instr = 1'b1;
        	                        end
        	                    end
        	                    5'b00101: begin
        	                        collect_instr_o.op = FMIN_MAX; 
        	                        check_fprm       = 1'b0;     
        	                        if (XF16ALT) begin           
        	                            if (!(instr_test.rftype.rm inside {[3'b000:3'b001], [3'b100:3'b101]})) //Wrong?? extra rounding modes
        	                                illegal_instr = 1'b1;
        	                        end else begin
        	                            if (!(instr_test.rftype.rm inside {[3'b000:3'b001]}))
        	                                illegal_instr = 1'b1;
        	                        end
        	                    end
        	                    5'b01000: begin
        	                        collect_instr_o.op  = FCVT_F2F; 
        	                        collect_instr_o.rs2 = instr_test.rvftype.rs1; 				//Wrong??
        	                	collect_instr_o.result = i_imm(tx_in.instruction_i);
        	        		collect_instr_o.use_imm = 1'b1;
        	                        if (instr_test.rftype.rs2[24:23]) illegal_instr = 1'b1; 
        	                        case (instr_test.rftype.rs2[22:20])
        	                            3'b000: if (~RVF)     illegal_instr = 1'b1;
        	                            3'b001: if (~RVD)     illegal_instr = 1'b1;
        	                            3'b010: if (~XF16)    illegal_instr = 1'b1;
        	                            3'b110: if (~XF16ALT) illegal_instr = 1'b1;
        	                            3'b011: if (~XF8)     illegal_instr = 1'b1;
        	                            default: illegal_instr = 1'b1;
        	                        endcase
        	                    end
        	                    5'b10100: begin
        	                        collect_instr_o.op = FCMP; 
        	                        check_fprm       = 1'b0; 
        	                        if (XF16ALT) begin      
        	                            if (!(instr_test.rftype.rm inside {[3'b000:3'b010], [3'b100:3'b110]})) // Wrong?? Extra rounding modes
        	                                illegal_instr = 1'b1;
        	                        end else begin
        	                            if (!(instr_test.rftype.rm inside {[3'b000:3'b010]}))
        	                                illegal_instr = 1'b1;
        	                        end
        	                    end
        	                    5'b11000: begin							
        	                        collect_instr_o.op = FCVT_F2I; 
        	                    	collect_instr_o.result = i_imm(tx_in.instruction_i);
        	        		collect_instr_o.use_imm = 1'b1;
        	                        if (instr_test.rftype.rs2[24:22]) illegal_instr = 1'b1; 
        	                    end
        	                    5'b11010: begin							
        	                        collect_instr_o.op = FCVT_I2F;  
        	                  	collect_instr_o.result = i_imm(tx_in.instruction_i);
        	        		collect_instr_o.use_imm = 1'b1;
        	                        if (instr_test.rftype.rs2[24:22]) illegal_instr = 1'b1; 
        	                    end
        	                    5'b11100: begin
        	                        collect_instr_o.rs2 = instr_test.rftype.rs1; 
        	                        check_fprm        = 1'b0; 
        	                        if (instr_test.rftype.rm == 3'b000 || (XF16ALT && instr_test.rftype.rm == 3'b100)) 
        	                            collect_instr_o.op = FMV_F2X;       
        	                        else if (instr_test.rftype.rm == 3'b001 || (XF16ALT && instr_test.rftype.rm == 3'b101)) 
        	                            collect_instr_o.op = FCLASS; 
        	                        else illegal_instr = 1'b1;
        	                        
        	                        if (instr_test.rftype.rs2 != 5'b00000) illegal_instr = 1'b1;
        	                    end
        	                    5'b11110: begin						
        	                        collect_instr_o.op = FMV_X2F; 
        	                        collect_instr_o.rs2 = instr_test.rftype.rs1; 
        	                        check_fprm       = 1'b0;
        	                        if (!(instr_test.rftype.rm == 3'b000 || (XF16ALT && instr_test.rftype.rm == 3'b100)))
        	                            illegal_instr = 1'b1;
        	                        if (instr_test.rftype.rs2 != 5'b00000) illegal_instr = 1'b1;
        	                    end
        	                    default : illegal_instr = 1'b1;
        	                endcase

        	                // check format
        	                case (instr_test.rftype.fmt)
        	                    2'b00: if (~RVF)             illegal_instr = 1'b1;
        	                    2'b01: if (~RVD)             illegal_instr = 1'b1;
        	                    2'b10: if (~XF16 & ~XF16ALT) illegal_instr = 1'b1;
        	                    2'b11: if (~XF8)             illegal_instr = 1'b1;
        	                    default: illegal_instr = 1'b1;
        	                endcase

        	                // check rounding mode
        	                if (check_fprm) begin
        	                    case (instr_test.rftype.rm) inside
        	                        [3'b000:3'b100]: ; 
        	                        3'b101: begin      
        	                            if (~XF16ALT || instr_test.rftype.fmt != 2'b10)
        	                                illegal_instr = 1'b1;
        	                            case (tx_in.frm_i) inside 
        	                                [3'b000:3'b100]: ;
        	                                default : illegal_instr = 1'b1;
        	                            endcase
        	                        end
        	                        3'b111: begin
        	                            case (tx_in.frm_i) inside
        	                                [3'b000:3'b100]: ; 
        	                                default : illegal_instr = 1'b1;
        	                            endcase
        	                        end
        	                        default : illegal_instr = 1'b1;
        	                    endcase
        	                end
        	            end else begin
        	                illegal_instr = 1'b1;
        	            end
		end

	////////////////////////////
	//Integer Reg Instructions//	
	///////////////////////////

		7'b0110011: begin
			if (instr_test.rvftype.funct2 != 2'b10) begin
		 		collect_instr_o.fu  = (instr_test.rtype.funct7 == 7'b000_0001) ? MULT : ALU;
		                collect_instr_o.rs1 = instr_test.rtype.rs1;
		                collect_instr_o.rs2 = instr_test.rtype.rs2;
		                collect_instr_o.rd  = instr_test.rtype.rd;

				if(instr_test.rtype.funct7 == 7'b000_0000) begin
					case (instr_test.rtype.funct3)
						3'b000 : collect_instr_o.op = ADD;   // Add
		                    	       	3'b010 : collect_instr_o.op = SLTS;  // Set Lower Than
		                    		3'b011 : collect_instr_o.op = SLTU;  // Set Lower Than Unsigned
		                    		3'b100 : collect_instr_o.op = XORL;  // Xor
		                    		3'b110 : collect_instr_o.op = ORL;   // Or
		                    		3'b111 : collect_instr_o.op = ANDL;  // And
		                    		3'b001 : collect_instr_o.op = SLL;   // Shift Left Logical
		                    		3'b101 : collect_instr_o.op = SRL;   // Shift Right Logical
						default: begin
		                                	illegal_instr = 1'b1;
                			        end
		                       	endcase
				end
				 else if(instr_test.rtype.funct7 == 7'b000_0001) begin
					// Multiplications
					case (instr_test.rtype.funct3)
		                    		3'b000 : collect_instr_o.op = MUL;
		                    		3'b001 : collect_instr_o.op = MULH;
		                    		3'b010 : collect_instr_o.op = MULHSU;
		                    		3'b011 : collect_instr_o.op = MULHU;
		                    		3'b100 : collect_instr_o.op = DIV;
		                    		3'b101 : collect_instr_o.op = DIVU;
		                    		3'b110 : collect_instr_o.op = REM;
		                    		3'b111 : collect_instr_o.op = REMU;
						default: begin
		                                	illegal_instr = 1'b1;
                			        end
					endcase
				end 
				else if(instr_test.rtype.funct7 == 7'b010_0000) begin
					case (instr_test.rtype.funct3)
						3'b000 : collect_instr_o.op = SUB;   // Sub
						3'b101 : collect_instr_o.op = SRA;   // Shift Right Arithmetic
						default: begin
		                                	illegal_instr = 1'b1;
                			        end
					endcase
				end
				else begin
		                	illegal_instr = 1'b1;
                		end
                	end
			else begin 
                                    illegal_instr = 1'b1;
                                end

                	end
				
				
		// --------------------------------
                // 32 bit Reg-Immediate Operations
                // --------------------------------

                7'b0011011: begin
                    collect_instr_o.fu  = ALU;
                    //imm_select = IIMM;
		    collect_instr_o.result = { {52 {instruction_i[31]}}, instruction_i[31:20] };
              	    collect_instr_o.use_imm = 1'b1;
                    collect_instr_o.rs1[4:0] = instr_test.itype.rs1;
                    collect_instr_o.rd[4:0]  = instr_test.itype.rd;

                    case (instr_test.itype.funct3)
                        3'b000: collect_instr_o.op = ADDW;  // Add Immediate

                        3'b001: begin
                          collect_instr_o.op = SLLW;  // Shift Left Logical by Immediate
                          if (instr_test.instr[31:25] != 7'b0)
                              illegal_instr = 1'b1;
                        end

                        3'b101: begin
                            if (instr_test.instr[31:25] == 7'b0)
                                collect_instr_o.op = SRLW;  // Shift Right Logical by Immediate
                            else if (instr_test.instr[31:25] == 7'b010_0000)
                                collect_instr_o.op = SRAW;  // Shift Right Arithmetically by Immediate
                            else
                                illegal_instr = 1'b1;
                        end

                        default: illegal_instr = 1'b1;
                    endcase
                end


	endcase
      end

        collect_instr_o.ex      = ex_i;
        collect_instr_o.valid   = ex_i.valid;
        if (~ex_i.valid) begin
            collect_instr_o.ex.tval  = (is_compressed_i) ? {48'b0, compressed_instr_i} : {32'b0, instruction_i};
            if (illegal_instr || is_illegal_i) begin
                collect_instr_o.valid    = 1'b1;
                collect_instr_o.ex.valid = 1'b1;
                collect_instr_o.ex.cause = riscv::ILLEGAL_INSTR;
            end else if (ecall) begin
                collect_instr_o.valid    = 1'b1;
                collect_instr_o.ex.valid = 1'b1;
                case (priv_lvl_i)
                    riscv::PRIV_LVL_M: collect_instr_o.ex.cause = riscv::ENV_CALL_MMODE;
                    riscv::PRIV_LVL_S: collect_instr_o.ex.cause = riscv::ENV_CALL_SMODE;
                    riscv::PRIV_LVL_U: collect_instr_o.ex.cause = riscv::ENV_CALL_UMODE;
                    default:; 
                endcase
            end else if (ebreak) begin
                collect_instr_o.valid    = 1'b1;
                collect_instr_o.ex.valid = 1'b1;
                collect_instr_o.ex.cause = riscv::BREAKPOINT;
            end
        end
	//`uvm_info("Scoreboard function",$sformatf("Instruction FU = %b",collect_instr_o.fu),UVM_LOW);
	return collect_instr_o;
endfunction


function logic decoder_scoreboard::getresult_cntrl_flow;
    logic [31:0]        instruction_i;           
    logic is_control_flow;
    riscv::instruction_t instr_test;

    instruction_i = tx_in.instruction_i;
    instr_test = riscv::instruction_t'(instruction_i);
    case (instr_test.rtype.opcode)
	7'b1100011: begin
 		is_control_flow = 1'b1;
                case (instr_test.stype.funct3)
		3'b010,3'b011: begin
                	is_control_flow = 1'b0;
		end
		endcase
	end
	7'b1100111: begin
 		is_control_flow = 1'b1;
	end
	7'b1101111: begin
 		is_control_flow = 1'b1;
	end
	default: begin
 		is_control_flow = 1'b0;
	end
    endcase
	return is_control_flow;
endfunction

endpackage: scoreboard
