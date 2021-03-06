`timescale 1ns / 100ps
import ariane_pkg::*;


module jrs_tb;    

logic [63:0] pc_i;
logic is_compressed_i;
logic [15:0] compressed_instr_i;

decoder decoder0(
.pc_i(pc_i),
.is_compressed_i(is_compressed_i),
.compressed_instr_i(compressed_instr_i)
	
);

initial begin
	pc_i = 64'h56577777;
	is_compressed_i = 1;
#500 
	
	pc_i = 64'h426738393;
	is_compressed_i = 0;

#500 
	
	pc_i = 64'h1234679;
	is_compressed_i = 1;
	
#2000 $finish;
end


endmodule: jrs_tb
