`include "uvm_macros.svh"
package coverage;
import sequences::*;
import uvm_pkg::*;
import ariane_pkg::*;

class decoder_subscriber_in extends uvm_subscriber #(decoder_transaction_in);
    `uvm_component_utils(decoder_subscriber_in)

    //Declare Variables
  /*  logic [31:0] A;
    logic [31:0] B;
    logic [4:0] opcode;
    logic cin;*/

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



    //TODO: Add covergroups for the inputs
    covergroup inputs;
    	cin1: coverpoint instruction_i { 	bins b1 = {32'hFFFFFFFF};
			   			bins b2 = {32'h00000000};
			   			bins b3 = {32'h7FFFFFFF};
			   			bins b4 = {32'h80000000};
			  		}
 	
	cin2: coverpoint instruction_i[6:0]{	bins b5 = {7'b0101111, 7'b0111011, 7'b1000011, 7'b0100011 };



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

        // TODO: Uncomment
        inputs.sample();
        
    endfunction: write

endclass: decoder_subscriber_in

class decoder_subscriber_out extends uvm_subscriber #(decoder_transaction_out);
    `uvm_component_utils(decoder_subscriber_out)

   /* logic [31:0] out;
    logic cout;
    logic vout;*/

    scoreboard_entry_t  instruction_o; 
    logic               is_control_flow_instr_o; 


    //TODO: Add covergroups for the outputs
    
    covergroup outputs;
	cout6: coverpoint is_control_flow_instr_o { 	bins b1 = {1'b1};
			      				bins b2 = {1'b0};
			  			  }

    endgroup: outputs
    

function new(string name, uvm_component parent);
    super.new(name,parent);
    // TODO: Uncomment
    outputs=new;
    
endfunction: new

function void write(decoder_transaction_out t);
  /*  out={t.OUT};
    cout={t.COUT};
    vout={t.VOUT};*/
    
    instruction_o = t.instruction_o;
    is_control_flow_instr_o = t.is_control_flow_instr_o;
    

    //TODO: Uncomment
    outputs.sample();

endfunction: write
endclass: decoder_subscriber_out

endpackage: coverage
