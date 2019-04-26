`timescale 1ns / 100ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import modules_pkg::*;
import sequences::*;
//import coverage::*;
import scoreboard::*;
import tests::*;

module dut(dut_in _in, dut_out _out);
decoder decoder0(
    .CLK(_in.clk),
    .RST(_in.rst),
    .pc_i(_in.pc_i),
    .is_compressed_i(_in.is_compressed_i),
    .compressed_instr_i(_in.compressed_instr_i),
    .is_illegal_i(_in.is_illegal_i),
    .instruction_i(_in.instruction_i),
    .branch_predict_i(_in.branch_predict_i),
    .ex_i(_in.ex_i),
    .priv_lvl_i(_in.priv_lvl_i),
    .debug_mode_i(_in.debug_mode_i),
    .fs_i(_in.fs_i),
    .frm_i(_in.frm_i),
    .tvm_i(_in.tvm_i),
    .tw_i(_in.tw_i),
    .tsr_i(_in.tsr_i),
    .instruction_o(_out.instruction_o),
    .is_control_flow_instr_o(_out.is_control_flow_instr_o)
);
endmodule: dut

module top;    
dut_in dut_in1();
dut_out dut_out1();

initial begin
    dut_in1.clk<=0;
    forever #50 dut_in1.clk<=~dut_in1.clk;
end

initial begin
    dut_out1.clk<=0;
    forever #50 dut_out1.clk<=~dut_out1.clk;
end

// TODO: Instantiate the dut module as dut1 and use the input as dut_in1 and output as dut_out1
dut dut1(
      ._in(dut_in1),
      ._out(dut_out1)
);

initial begin
    uvm_config_db #(virtual dut_in)::set(null,"uvm_test_top","dut_vi_in",dut_in1);
    uvm_config_db #(virtual dut_out)::set(null,"uvm_test_top","dut_vi_out",dut_out1);
    uvm_top.finish_on_completion=1;

    //TODO:Modify the test name here
    run_test("test1");
end

endmodule: top
