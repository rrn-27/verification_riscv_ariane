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
	rand logic [24:0]	 rest_i;                  
	
        //TODO: Add constraints here

      	constraint restrict_ex_valid {(ex_i.valid == 0);} // Restrict for no exception case
      	constraint restrict_load_store {((opcode ==7'b0100011) || (opcode ==7'b0000011));}
      	constraint restrict_store_legal {(opcode ==7'b0100011)->((funct3 == 3'b000) ||(funct3 == 3'b001) || (funct3 == 3'b010) || (funct3 == 3'b011));}
      	constraint restrict_load_legal {(opcode ==7'b0000011)->((funct3 == 3'b000) ||(funct3 == 3'b001) || (funct3 == 3'b010) || (funct3 == 3'b011) || (funct3 == 3'b100) || (funct3 == 3'b101) || (funct3 == 3'b110));}
	constraint restrict_atomic_legal{(opcode==7'b0101111);}
	constraint restrict_32_regreg{(opcode==7'b0111011);}
	constraint restrict_fp_32_regreg_legal{(opcode==7'b1000011)||(opcode==7'b1000111)|| (opcode==7'b1001011)||(opcode== 7'b1001111)||(opcode== 7'b1010011) ;}
	constraint restrict_control_legal{(opcode==7'b1100011) || (opcode==7'b1100111) || (opcode==7'b1101111) || (opcode==7'b0010111) || (opcode==7'b0010111);}

	//shvetha constraints
	constraint restrict_integer_reg{(opcode==7'b0110011)->((funct7==7'b0000000)||(funct7==7'b0100000)||(funct7==7'b0000001));}
	
	constraint restrict_reg_imm_funct3{(opcode==7'b0011011)->((funct3==3'b000)||(funct3==3'b001)||(funct3==101));}
	constraint restrict_reg_imm_funct7_sll{((opcode==7'b0011011)&&(funct3==3'b001))->(funct7==7'b0000000);}
	constraint restrict_reg_imm_funt7_srl_sra{((opcode==7'b0011011)&&(funct3==3'b101))->((funct7==7'b0000000)||(funct7==7'b0100000));}
	
	constraint restrict_vec_float{(opcode==7'b0110011)->(instruction_i[31:30] == 2'b10);} 

        function new(string name = "");
            super.new(name);
        endfunction: new

        function string convert2string;
            convert2string={$sformatf("Instruction = %b",instruction_i)};
        endfunction: convert2string
	
	function void post_randomize();
		if((opcode == 7'b0100011)||(opcode == 7'b0110011)||(opcode == 7'b0011011)) begin
			instruction_i[31:0] = {imm[11:5],rs2[4:0],rs1[4:0],funct3,imm[4:0],opcode};
		end
		else if(opcode == 7'b0000011) begin
			instruction_i[31:0] = {imm[11:0],rs1,funct3,rd[4:0],opcode};
		end
		else begin
			instruction_i[31:0] = {rest_i,opcode};
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
	    tx.restrict_integer_reg.constraint_mode(0);
	    tx.restrict_reg_imm_funct3.constraint_mode(0);
	    tx.restrict_reg_imm_funct7_sll.constraint_mode(0);
	    tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(0);
	    tx.restrict_vec_float.constraint_mode(0);

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
	    tx.restrict_integer_reg.constraint_mode(0);
            tx.restrict_reg_imm_funct3.constraint_mode(0);
            tx.restrict_reg_imm_funct7_sll.constraint_mode(0);
            tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(0);
            tx.restrict_vec_float.constraint_mode(0);

            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_atom

class seq_32_regreg extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_32_regreg)

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
	    tx.restrict_32_regreg.constraint_mode(1);
	    tx.restrict_fp_32_regreg_legal.constraint_mode(0);
	    tx.restrict_control_legal.constraint_mode(0);
            tx.restrict_integer_reg.constraint_mode(0);
            tx.restrict_reg_imm_funct3.constraint_mode(0);
            tx.restrict_reg_imm_funct7_sll.constraint_mode(0);
            tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(0);
            tx.restrict_vec_float.constraint_mode(0);

	    start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_32_regreg

class seq_fp_32_regreg extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_fp_32_regreg)

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
	    tx.restrict_atomic_legal.constraint_mode(0);
	    tx.restrict_32_regreg.constraint_mode(0);
	    tx.restrict_fp_32_regreg_legal.constraint_mode(1);
	    tx.restrict_control_legal.constraint_mode(0);
	    tx.restrict_integer_reg.constraint_mode(0);
            tx.restrict_reg_imm_funct3.constraint_mode(0);
            tx.restrict_reg_imm_funct7_sll.constraint_mode(0);
            tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(0);
            tx.restrict_vec_float.constraint_mode(0);

            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_fp_32_regreg

class seq_control extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_control)

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
	    tx.restrict_atomic_legal.constraint_mode(0);
	    tx.restrict_32_regreg.constraint_mode(0);
	    tx.restrict_fp_32_regreg_legal.constraint_mode(0);
	    tx.restrict_control_legal.constraint_mode(1);
	    tx.restrict_integer_reg.constraint_mode(0);
            tx.restrict_reg_imm_funct3.constraint_mode(0);
            tx.restrict_reg_imm_funct7_sll.constraint_mode(0);
            tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(0);
            tx.restrict_vec_float.constraint_mode(0);

            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_control

class seq_int_reg extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_control)

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
            tx.restrict_atomic_legal.constraint_mode(0);
            tx.restrict_32_regreg.constraint_mode(0);
            tx.restrict_fp_32_regreg_legal.constraint_mode(0);
            tx.restrict_control_legal.constraint_mode(0);
	    tx.restrict_integer_reg.constraint_mode(1);
            tx.restrict_reg_imm_funct3.constraint_mode(0);
            tx.restrict_reg_imm_funct7_sll.constraint_mode(0);
            tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(0);
            tx.restrict_vec_float.constraint_mode(0);

            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_int_reg

class seq_reg_imm extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_control)

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
            tx.restrict_atomic_legal.constraint_mode(0);
            tx.restrict_32_regreg.constraint_mode(0);
            tx.restrict_fp_32_regreg_legal.constraint_mode(0);
            tx.restrict_control_legal.constraint_mode(0);
            tx.restrict_integer_reg.constraint_mode(0);
            tx.restrict_reg_imm_funct3.constraint_mode(1);
            tx.restrict_reg_imm_funct7_sll.constraint_mode(1);
            tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(1);
            tx.restrict_vec_float.constraint_mode(0);

	    start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_reg_imm

class seq_vec_float extends uvm_sequence #(decoder_transaction_in);
        `uvm_object_utils(seq_control)

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
            tx.restrict_atomic_legal.constraint_mode(0);
            tx.restrict_32_regreg.constraint_mode(0);
            tx.restrict_fp_32_regreg_legal.constraint_mode(0);
            tx.restrict_control_legal.constraint_mode(0);
            tx.restrict_integer_reg.constraint_mode(0);
            tx.restrict_reg_imm_funct3.constraint_mode(0);
            tx.restrict_reg_imm_funct7_sll.constraint_mode(0);
            tx.restrict_reg_imm_funt7_srl_sra.constraint_mode(0);
            tx.restrict_vec_float.constraint_mode(1);

	    start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
        endtask: body
    endclass: seq_vec_float



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
           	seq_atom seq2;
           	seq_32_regreg seq3;
           	seq_fp_32_regreg seq4;
           	seq_control seq5;
		seq_int_reg seq6;
		seq_reg_imm seq7;
		seq_vec_float seq8;                

		seq = simple_seq::type_id::create("seq");
                seq2 = seq_atom::type_id::create("seq2");
                seq3 = seq_32_regreg::type_id::create("seq3");
                seq4 = seq_fp_32_regreg::type_id::create("seq4");
                seq5 = seq_control::type_id::create("seq5");
		seq6 = seq_int_reg::type_id::create("seq6");
		seq7 = seq_reg_imm::type_id::create("seq7");
		seq8 = seq_vec_float::type_id::create("seq8");

                assert( seq.randomize() );
                seq.start(p_sequencer);

	        assert( seq2.randomize() );
                seq2.start(p_sequencer);

	        assert( seq3.randomize() );
                seq3.start(p_sequencer);

	        assert( seq4.randomize() );
                seq4.start(p_sequencer);

	        assert( seq5.randomize() );
                seq5.start(p_sequencer);

		assert( seq6.randomize() );
                seq6.start(p_sequencer);

		assert( seq7.randomize() );
                seq7.start(p_sequencer);

		assert( seq8.randomize() );
                seq8.start(p_sequencer);

            end
        endtask: body

    endclass: seq_of_commands

endpackage: sequences
