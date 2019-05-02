`include "uvm_macros.svh"
package sequences;
    
import ariane_pkg::*;
    import uvm_pkg::*;

    class decoder_transaction_in extends uvm_sequence_item;
         // TODO: Register the  decoder_transaction_in object. Hint: Look at other classes to find out what is missing.
       `uvm_object_utils(decoder_transaction_in);


    	rand logic [63:0]        pc_i;                    
    	rand logic               is_compressed_i;
    	rand logic [15:0]        compressed_instr_i;     
    	rand logic               is_illegal_i;            
    	logic [31:0]        	instruction_i;           
	rand logic [6:0] 	opcode;
	rand logic [4:0] 	rs1;
	rand logic [4:0] 	rs2;
	rand logic [4:0] 	rd;
	rand logic [12:0]	imm;
	rand logic [2:0] 	funct3;
	rand logic [6:0] 	funct7;
    	rand branchpredict_sbe_t branch_predict_i;
    	rand exception_t         ex_i;                    
    	rand riscv::priv_lvl_t   priv_lvl_i;              
    	rand logic               debug_mode_i;
    	rand riscv::xs_t         fs_i;               
    	rand logic [2:0]         frm_i;                   
    	rand logic               tvm_i;                   
    	rand logic               tw_i;                   
	
	
        //TODO: Add constraints here

      	constraint restrict_ex_valid {(ex_i.valid == 0);} // Restrict for no exception case
      	constraint restrict_load_store {((opcode ==7'b0100011) || (opcode ==7'b0000011));}
      	constraint restrict_store_legal {(opcode ==7'b0100011)->((funct3 == 3'b000) ||(funct3 == 3'b001) || (funct3 == 3'b010) || (funct3 == 3'b011));}
      	constraint restrict_load_legal {(opcode ==7'b0000011)->((funct3 == 3'b000) ||(funct3 == 3'b001) || (funct3 == 3'b010) || (funct3 == 3'b011) || (funct3 == 3'b100) || (funct3 == 3'b101) || (funct3 == 3'b110));}
	constraint restrict_atomic_legal{(opcode==7'b0101111);}
	constraint restrict_32_regreg{(opcode==7'b0111011);}
	constraint restrict_fp_32_regreg_legal{(opcode==7'b1000011)||(opcode==7'b1000111)|| (opcode==7'b1001011)||(opcode== 7'b1001111)||(opcode== 7'b1010011) ;}
	constraint restrict_control_legal{(opcode==7'b1100011) || (opcode==7'b1100111) || (opcode==7'b1101111) || (opcode==7'b0010111) || (opcode==7'b0010111);}
 

        function new(string name = "");
            super.new(name);
        endfunction: new

        function string convert2string;
            convert2string={$sformatf("Instruction = %b",instruction_i)};
        endfunction: convert2string
	
	function void post_randomize();
		if(opcode == 7'b0100011) begin
			instruction_i[31:0] = {imm[11:5],rs2[4:0],rs1[4:0],funct3,imm[4:0],opcode};
		end
		else if(opcode == 7'b0000011) begin
			instruction_i[31:0] = {imm[11:0],rs1,funct3,rd[4:0],opcode};
		end
	endfunction: post_randomize

    endclass: decoder_transaction_in


    class decoder_transaction_out extends uvm_sequence_item;
        // TODO: Register the  decoder_transaction_out object. Hint: Look at other classes to find out what is missing.
       `uvm_object_utils(decoder_transaction_out);

   	scoreboard_entry_t  instruction_o;
	logic               is_control_flow_instr_o;
	
        function new(string name = "");
            super.new(name);
        endfunction: new;
        
        function string convert2string;
            convert2string={$sformatf("PC = %b\n",instruction_o.pc)};
        endfunction: convert2string

    endclass: decoder_transaction_out

    class simple_seq extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
	    tx.restrict_ex_valid.constraint_mode(1);
      	    tx.restrict_load_store.constraint_mode(1);
      	    tx.restrict_store_legal.constraint_mode(1);
      	    tx.restrict_load_legal.constraint_mode(1);
	    tx.restrict_atomic_legal.constraint_mode(0);
	    tx.restrict_32_regreg.constraint_mode(0);
	    tx.restrict_fp_32_regreg_legal.constraint_mode(0);
	    tx.restrict_control_legal.constraint_mode(0);
	    
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq

class seq_atom extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_atom)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
	    tx.restrict_ex_valid.constraint_mode(1);
      	    tx.restrict_load_store.constraint_mode(0);
      	    tx.restrict_store_legal.constraint_mode(0);
      	    tx.restrict_load_legal.constraint_mode(0);
	    tx.restrict_atomic_legal.constraint_mode(1);
	    tx.restrict_32_regreg.constraint_mode(0);
	    tx.restrict_fp_32_regreg_legal.constraint_mode(0);
	    tx.restrict_control_legal.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_atom


/*class simple_seq_4 extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_4)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(1);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_4


class simple_seq_5 extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_5)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(1);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_5

class simple_seq_6 extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_6)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            tx.rst_set.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_6


    class simple_seq_random extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_random)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(1);
            tx.arith_add_sub_bug_a.constraint_mode(0);
            tx.arith_add_sub_bug_b.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_random

class simple_seq_2_random extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_2_random)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(1);
            tx.shift_bug_a.constraint_mode(0);
            tx.shift_bug_b.constraint_mode(0);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_2_random


class simple_seq_3_random extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_3_random)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(1);
            tx.compare_bug_a.constraint_mode(0);
            tx.compare_bug_b.constraint_mode(0);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_3_random

class simple_seq_4_random extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_4_random)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(1);
            tx.logical_bug_a.constraint_mode(0);
            tx.logical_bug_b.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_4_random*/


    class seq_of_commands extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_of_commands)
        `uvm_declare_p_sequencer(uvm_sequencer#(decoder_transaction_in))

        function new (string name = "");
            super.new(name);
        endfunction: new

        task body;
            repeat(15000)
            begin
                simple_seq seq;
                seq = simple_seq::type_id::create("seq");

                assert( seq.randomize() );
                seq.start(p_sequencer);

            end
        endtask: body

    endclass: seq_of_commands

endpackage: sequences
