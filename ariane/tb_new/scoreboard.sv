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
    instr_check = getresult_scoreboard_entry();
    instr_output = tx_out.instruction_o;

    if(instr_check.pc != instr_output.pc) begin
	`uvm_info("Compare_failed",$sformatf("Expected = %b Got = %b",instr_check.pc,instr_output.pc),UVM_LOW);

//|| (instr_check.fu != instr_output.fu) || (instr_check.op != instr_output.op) || (instr_check.rs1 != instr_output.rs1) || (instr_check.rs2 != instr_output.rs2) || (instr_check.rd != instr_output.rd) || (instr_check.result != instr_output.result) || (instr_check.valid != instr_output.valid) || (instr_check.use_imm != instr_output.use_imm) || (instr_check.use_pc != instr_output.use_pc) ||  (instr_check.bp != instr_output.bp) || (instr_check.is_compressed != instr_output.is_compressed)) begin
    end
    else begin
	`uvm_info("Compare_success","Decoder output equal",UVM_LOW);
//	`uvm_info("Compare_success",tx_out.convert2string(),UVM_LOW);
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
//REVISIT this
    logic ecall;
    logic ebreak;              
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
	
        collect_instr_o.result        = 64'b0;
        collect_instr_o.use_imm        = 1'b0;
       // is_control_flow_instr_o     = 1'b0;
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
        //check_fprm                  = 1'b0;

            case (instr_test.rtype.opcode)
               0100011: begin
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

                0000011: begin
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

                0100111: begin
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

                0000111: begin
                    if (FP_PRESENT && fs_i != riscv::Off) begin // only generate decoder if FP extensions are enabled (static)
                        collect_instr_o.fu  = LOAD;
               	        collect_instr_o.result =  {{52 {instruction_i[31]}}, instruction_i[31:20]};
                        collect_instr_o.use_imm = 1'b1;
                        collect_instr_o.rs1       = instr_test.itype.rs1;
                        collect_instr_o.rd        = instr_test.itype.rd;
                        // determine load size
                        case (instr_test.itype.funct3)
                            // Only process instruction if corresponding extension is active (static)
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

                0010011: begin
                    collect_instr_o.fu  = ALU;
               	    collect_instr_o.result =  {{52 {instruction_i[31]}}, instruction_i[31:20]};
                    collect_instr_o.use_imm = 1'b1;
                    collect_instr_o.rs1[4:0] = instr_test.itype.rs1;
                    collect_instr_o.rd[4:0]  = instr_test.itype.rd;

                    case (instr_test.itype.funct3)
                        3'b000: collect_instr_o.op = ADD;   // Add Immediate
                        3'b010: collect_instr_o.op = SLTS;  // Set to one if Lower Than Immediate
                        3'b011: collect_instr_o.op = SLTU;  // Set to one if Lower Than Immediate Unsigned
                        3'b100: collect_instr_o.op = XORL;  // Exclusive Or with Immediate
                        3'b110: collect_instr_o.op = ORL;   // Or with Immediate
                        3'b111: collect_instr_o.op = ANDL;  // And with Immediate

                        3'b001: begin
                          collect_instr_o.op = SLL;  // Shift Left Logical by Immediate
                          if (instr_test.instr[31:26] != 6'b0)
                            illegal_instr = 1'b1;
                        end

                        3'b101: begin
                            if (instr_test.instr[31:26] == 6'b0)
                                collect_instr_o.op = SRL;  // Shift Right Logical by Immediate
                            else if (instr_test.instr[31:26] == 6'b010_000)
                                collect_instr_o.op = SRA;  // Shift Right Arithmetically by Immediate
                            else
                                illegal_instr = 1'b1;
                        end
                    endcase
                end

	endcase

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
                    default:; // this should not happen
                endcase
            end else if (ebreak) begin
                collect_instr_o.valid    = 1'b1;
                collect_instr_o.ex.valid = 1'b1;
                collect_instr_o.ex.cause = riscv::BREAKPOINT;
            end
        end
	return collect_instr_o;
endfunction


function logic decoder_scoreboard::getresult_cntrl_flow;
    logic [31:0]        instruction_i;           

    instruction_i = tx_in.instruction_i;
    getresult_cntrl_flow = 1;

endfunction

endpackage: scoreboard
