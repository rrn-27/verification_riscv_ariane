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

    extern virtual function [33:0] getresult; 
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
    
endfunction

function scoreboard_entry_t decoder_scoreboard::getresult_scoreboard_entry;
    //TODO: Remove the statement below
    //Modify this function to return a 34-bit result {VOUT, COUT,OUT[31:0]} which is
    //consistent with the given spec.

    riscv::instruction_t instr_test;
    assign instr_test = riscv::instruction_t'(instruction_i);

    case (instr.rtype.opcode)





    endcase


//  Write a default return value
//    return 34'd0;
endfunction


function decoder_scoreboard::getresult_cntrl_flow;

endfunction

endpackage: scoreboard
