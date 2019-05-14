`include "uvm_macros.svh"
package modules_pkg;

import uvm_pkg::*;
import sequences::*;
import coverage::*;
import scoreboard::*;

typedef uvm_sequencer #(decoder_transaction_in) decoder_sequencer_in;

class decoder_dut_config extends uvm_object;
    `uvm_object_utils(decoder_dut_config)

    virtual dut_in dut_vi_in;
    virtual dut_out dut_vi_out;

endclass: decoder_dut_config

class decoder_driver_in extends uvm_driver#(decoder_transaction_in);
    `uvm_component_utils(decoder_driver_in)

    decoder_dut_config dut_config_0;
    virtual dut_in dut_vi_in;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
       assert( uvm_config_db #(decoder_dut_config)::get(this, "", "dut_config", dut_config_0));
       dut_vi_in = dut_config_0.dut_vi_in;
    endfunction : build_phase
   
    task run_phase(uvm_phase phase);
      forever
      begin
        decoder_transaction_in tx;
        
        @(posedge dut_vi_in.clk);
        seq_item_port.get(tx);
        
        // TODO: Drive values from decoder_transaction_in onto the virtual
        // interface of dut_vi_in
        dut_vi_in.pc_i 			<= tx.pc_i;
        dut_vi_in.is_compressed_i 	<= tx.is_compressed_i;
        dut_vi_in.compressed_instr_i 	<= tx.compressed_instr_i;
        dut_vi_in.is_illegal_i 		<= tx.is_illegal_i;
        dut_vi_in.instruction_i 	<= tx.instruction_i;		
        dut_vi_in.branch_predict_i	<= tx.branch_predict_i;		
        dut_vi_in.instruction_i 	<= tx.instruction_i;		
        dut_vi_in.ex_i		 	<= tx.ex_i;		
        dut_vi_in.priv_lvl_i	 	<= tx.priv_lvl_i;		
        dut_vi_in.debug_mode_i	 	<= tx.debug_mode_i;		
        dut_vi_in.fs_i		 	<= tx.fs_i;		
        dut_vi_in.frm_i		 	<= tx.frm_i;		
        dut_vi_in.tvm_i		 	<= tx.tvm_i;		
        dut_vi_in.tw_i		 	<= tx.tw_i;		

      end
    endtask: run_phase

endclass: decoder_driver_in

class decoder_monitor_in extends uvm_monitor;
    `uvm_component_utils(decoder_monitor_in)

    uvm_analysis_port #(decoder_transaction_in) aport;

    decoder_dut_config dut_config_0;

    virtual dut_in dut_vi_in;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        dut_config_0=decoder_dut_config::type_id::create("config");
        aport=new("aport",this);
        assert( uvm_config_db #(decoder_dut_config)::get(this, "", "dut_config", dut_config_0) );
        dut_vi_in=dut_config_0.dut_vi_in;

    endfunction: build_phase

    task run_phase(uvm_phase phase);
    @(posedge dut_vi_in.clk);
      forever
      begin
        decoder_transaction_in tx;
        @(posedge dut_vi_in.clk);
        tx = decoder_transaction_in::type_id::create("tx");
        // TODO: Read the values from the virtual interface of dut_vi_in and
        // assign them to the transaction "tx"

	tx.pc_i                     =  dut_vi_in.pc_i;
	tx.is_compressed_i          =  dut_vi_in.is_compressed_i;
	tx.compressed_instr_i       =  dut_vi_in.compressed_instr_i;
	tx.is_illegal_i             =  dut_vi_in.is_illegal_i;
	tx.instruction_i	    =  dut_vi_in.instruction_i;    
	tx.branch_predict_i	    =  dut_vi_in.branch_predict_i;       
	tx.instruction_i	    =  dut_vi_in.instruction_i;       
	tx.ex_i		     	    =  dut_vi_in.ex_i;
	tx.priv_lvl_i	            =  dut_vi_in.priv_lvl_i;      
	tx.debug_mode_i	     	    =  dut_vi_in.debug_mode_i;      
	tx.fs_i		            =  dut_vi_in.fs_i;
	tx.frm_i		    =  dut_vi_in.frm_i;       
	tx.tvm_i		    =  dut_vi_in.tvm_i;       
	tx.tw_i		            =  dut_vi_in.tw_i;



        aport.write(tx);
      end
    endtask: run_phase

endclass: decoder_monitor_in


class decoder_monitor_out extends uvm_monitor;
    `uvm_component_utils(decoder_monitor_out)

    uvm_analysis_port #(decoder_transaction_out) aport;

    decoder_dut_config dut_config_0;

    virtual dut_out dut_vi_out;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        dut_config_0=decoder_dut_config::type_id::create("config");
        aport=new("aport",this);
        assert( uvm_config_db #(decoder_dut_config)::get(this, "", "dut_config", dut_config_0) );
        dut_vi_out=dut_config_0.dut_vi_out;

    endfunction: build_phase

    task run_phase(uvm_phase phase);
    @(posedge dut_vi_out.clk);
    @(posedge dut_vi_out.clk);
      forever
      begin
        decoder_transaction_out tx;
        
        @(posedge dut_vi_out.clk);
        tx = decoder_transaction_out::type_id::create("tx");
        // TODO: Read the values from the virtual interface of dut_vi_out and
        // assign them to the transaction "tx"
        
        
   	tx.instruction_o = dut_vi_out.instruction_o;
	tx.is_control_flow_instr_o = dut_vi_out.is_control_flow_instr_o;

        aport.write(tx);
      end
    endtask: run_phase
endclass: decoder_monitor_out

class decoder_agent_in extends uvm_agent;
    `uvm_component_utils(decoder_agent_in)

    uvm_analysis_port #(decoder_transaction_in) aport;

    decoder_sequencer_in decoder_sequencer_in_h;
    decoder_driver_in decoder_driver_in_h;
    decoder_monitor_in decoder_monitor_in_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new


    function void build_phase(uvm_phase phase);
        aport=new("aport",this);
        decoder_sequencer_in_h=decoder_sequencer_in::type_id::create("decoder_sequencer_in_h",this);
        decoder_driver_in_h=decoder_driver_in::type_id::create("decoder_driver_in_h",this);
        decoder_monitor_in_h=decoder_monitor_in::type_id::create("decoder_monitor_in_h",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        decoder_driver_in_h.seq_item_port.connect(decoder_sequencer_in_h.seq_item_export);
        decoder_monitor_in_h.aport.connect(aport);
    endfunction: connect_phase

endclass: decoder_agent_in

class decoder_agent_out extends uvm_agent;
    `uvm_component_utils(decoder_agent_out)

    uvm_analysis_port #(decoder_transaction_out) aport;

    decoder_monitor_out decoder_monitor_out_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        aport=new("aport",this);
        decoder_monitor_out_h=decoder_monitor_out::type_id::create("decoder_monitor_out_h",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        decoder_monitor_out_h.aport.connect(aport);
    endfunction: connect_phase

endclass: decoder_agent_out


class decoder_env extends uvm_env;
    `uvm_component_utils(decoder_env)

    decoder_agent_in decoder_agent_in_h;
    decoder_agent_out decoder_agent_out_h;
    decoder_subscriber_in decoder_subscriber_in_h;
    decoder_subscriber_out decoder_subscriber_out_h;
    decoder_scoreboard decoder_scoreboard_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        decoder_agent_in_h = decoder_agent_in::type_id::create("decoder_agent_in_h",this);
        decoder_agent_out_h = decoder_agent_out::type_id::create("decoder_agent_out_h",this);
        decoder_subscriber_in_h = decoder_subscriber_in::type_id::create("decoder_subscriber_in_h",this);
        decoder_subscriber_out_h = decoder_subscriber_out::type_id::create("decoder_subscriber_out_h",this);
        decoder_scoreboard_h = decoder_scoreboard::type_id::create("decoder_scoreboard_h",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        decoder_agent_in_h.aport.connect(decoder_subscriber_in_h.analysis_export);
        decoder_agent_out_h.aport.connect(decoder_subscriber_out_h.analysis_export);
        decoder_agent_in_h.aport.connect(decoder_scoreboard_h.sb_in);
        decoder_agent_out_h.aport.connect(decoder_scoreboard_h.sb_out);
    endfunction: connect_phase

    function void start_of_simulation_phase(uvm_phase phase);
        //TODO: Use this command to set the verbosity of the testbench. By
        //default, it is UVM_MEDIUM
        uvm_top.set_report_verbosity_level_hier(UVM_HIGH);
    endfunction: start_of_simulation_phase

endclass: decoder_env

class decoder_test extends uvm_test;
    `uvm_component_utils(decoder_test)

    decoder_dut_config dut_config_0;
    decoder_env decoder_env_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        dut_config_0 = new();
        if(!uvm_config_db #(virtual dut_in)::get( this, "", "dut_vi_in", dut_config_0.dut_vi_in))
          `uvm_fatal("NOVIF", "No virtual interface set for dut_in")
        
        if(!uvm_config_db #(virtual dut_out)::get( this, "", "dut_vi_out", dut_config_0.dut_vi_out))
          `uvm_fatal("NOVIF", "No virtual interface set for dut_out")
            
        uvm_config_db #(decoder_dut_config)::set(this, "*", "dut_config", dut_config_0);
        decoder_env_h = decoder_env::type_id::create("decoder_env_h", this);
    endfunction: build_phase

endclass:decoder_test

endpackage: modules_pkg
