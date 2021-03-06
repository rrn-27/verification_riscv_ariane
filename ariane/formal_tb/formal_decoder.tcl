#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script
clear -all

#Reading the files (.v and .sv) 
analyze -sv ../src/riscv-dbg/src/dm_pkg.sv ../include/riscv_pkg.sv ../include/ariane_pkg.sv ../src/id_stage.sv ../src/instr_realigner.sv ../src/compressed_decoder.sv ../src/decoder.sv
analyze -sv bind_wrapper_decoder.sv

#Elaborating the design, specify the top module
elaborate -top id_stage -bbox_m compressed_decoder -bbox_m instr_realigner

#You may  need to add commands below

#Set the clock
clock clk_i 
#Set Reset

reset ~rst_ni

#Prove all
prove -bg -all
