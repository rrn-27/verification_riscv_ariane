#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script
clear -all

#Reading the files (.v and .sv) 
analyze -sv ../src/riscv-dbg/src/dm_pkg.sv ../include/riscv_pkg.sv ../include/ariane_pkg.sv ../src/alu.sv
analyze -sv bind_wrapper.sv

#Elaborating the design, specify the top module
elaborate -top alu

#You may  need to add commands below

#Set the clock
clock clk_i
#Set Reset
reset ~rst_ni

#Prove all
prove -bg -all
