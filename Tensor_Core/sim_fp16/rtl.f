-sverilog               // Support SystemVerilog 
-timescale=1ns/1ps      // 

//+define+POWER_EST
//+define+SAED32

// ===================================================
// RTL 
// ===================================================
../tensor_core_gemm.v
../tensor_core_mma.v
../tensor_core_top.v

../../Multiplication/fp16_mul.v
../../Addition_and_Subtraction/fp16_add.v
../../Accumulation/kulisch_acc_fp16.v

// ===================================================
// SRAM 
// ===================================================
