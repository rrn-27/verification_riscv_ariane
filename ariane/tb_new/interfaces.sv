import ariane_pkg::*;
interface dut_in;
    logic           	clk, reset_n;
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
    logic               tsr_i;   
endinterface: dut_in


interface dut_out;
    logic	clk;
 //TODO: Complete the dut_out interface
    scoreboard_entry_t  instruction_o;
    logic               is_control_flow_instr_o;

endinterface: dut_out
