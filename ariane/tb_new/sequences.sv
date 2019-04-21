`include "uvm_macros.svh"
package sequences;

    import uvm_pkg::*;

    class decoder_transaction_in extends uvm_sequence_item;
         // TODO: Register the  decoder_transaction_in object. Hint: Look at other classes to find out what is missing.
       `uvm_object_utils(decoder_transaction_in);


    	rand logic [63:0]        pc_i;                    
    	rand logic               is_compressed_i;
    	rand logic [15:0]        compressed_instr_i;     
    	rand logic               is_illegal_i;            
    	rand logic [31:0]        instruction_i;           
	//REVISIT this
    	rand branchpredict_sbe_t branch_predict_i;
	//REVISIT this
    	rand exception_t         ex_i;                    
	//REVISIT this
    	rand riscv::priv_lvl_t   priv_lvl_i;              
    	rand logic               debug_mode_i;
	//REVISIT this
    	rand riscv::xs_t         fs_i;               
    	rand logic [2:0]         frm_i;                   
    	rand logic               tvm_i;                   
    	rand logic               tw_i;                   

        //TODO: Add constraints here

       

        function new(string name = "");
            super.new(name);
        endfunction: new

        function string convert2string;
            convert2string={$sformatf("Operand A = %b, Operand B = %b, Opcode = %b, CIN = %b",A,B,opcode,CIN)};
        endfunction: convert2string

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
            convert2string={$sformatf("OUT = %b, COUT = %b, VOUT = %b",OUT,COUT,VOUT)};
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
            tx.restrict_arith_add_sub.constraint_mode(1);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq

class simple_seq_2 extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_2)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(1);
            tx.restrict_compare.constraint_mode(0);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_2


class simple_seq_3 extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(simple_seq_3)

        function new(string name = "");
            super.new(name);
        endfunction: new

        task body;
            decoder_transaction_in tx;
            tx=decoder_transaction_in::type_id::create("tx");
            tx.restrict_arith_add_sub.constraint_mode(0);
            tx.restrict_shift_operations.constraint_mode(0);
            tx.restrict_compare.constraint_mode(1);
            tx.restrict_logical.constraint_mode(0);
            tx.restrict_unused.constraint_mode(0);
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: simple_seq_3

class simple_seq_4 extends uvm_sequence #(decoder_transaction_in);
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
    endclass: simple_seq_4_random


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
                simple_seq_2 seq_2;
                simple_seq_3 seq_3;
                simple_seq_4 seq_4;
                simple_seq_5 seq_5;
                simple_seq_6 seq_6;
                simple_seq_random seq_rand;
                simple_seq_2_random seq_2_rand;
                simple_seq_3_random seq_3_rand;
                simple_seq_4_random seq_4_rand;
                seq = simple_seq::type_id::create("seq");
                seq_2 = simple_seq_2::type_id::create("seq_2");
                seq_3 = simple_seq_3::type_id::create("seq_3");
                seq_4 = simple_seq_4::type_id::create("seq_4");
                seq_5 = simple_seq_5::type_id::create("seq_5");
                seq_6 = simple_seq_6::type_id::create("seq_6");
                seq_rand = simple_seq_random::type_id::create("seq_rand");
                seq_2_rand = simple_seq_2_random::type_id::create("seq_2_rand");
                seq_3_rand = simple_seq_3_random::type_id::create("seq_3_rand");
                seq_4_rand = simple_seq_4_random::type_id::create("seq_4_rand");

                assert( seq.randomize() );
                seq.start(p_sequencer);

                assert( seq_2.randomize() );
                seq_2.start(p_sequencer);

                assert( seq_3.randomize() );
                seq_3.start(p_sequencer);

               assert( seq_4.randomize() );
                seq_4.start(p_sequencer);

               assert( seq_5.randomize() );
               seq_5.start(p_sequencer);

                assert( seq_6.randomize() );
               seq_6.start(p_sequencer);

              assert( seq_rand.randomize() );
              seq_rand.start(p_sequencer);

               assert( seq_2_rand.randomize() );
              seq_2_rand.start(p_sequencer);

               assert( seq_3_rand.randomize() );
              seq_3_rand.start(p_sequencer);

               assert( seq_4_rand.randomize() );
               seq_4_rand.start(p_sequencer);

            end
        endtask: body

    endclass: seq_of_commands

endpackage: sequences
