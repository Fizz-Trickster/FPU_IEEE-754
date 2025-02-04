verdiSetActWin -dock widgetDock_<Decl._Tree>
simSetSimulator "-vcssv" -exec "simv" -args "-a vcs.log"
debImport "-dbdir" "simv.daidir"
debLoadSimResult \
           /home/ysyoon/PROJECT/FPU_IEEE-754/Tensor_Core/sim_fp16/waveform.fsdb
wvCreateWindow
verdiWindowResize -win $_Verdi_1 "1810" "610" "900" "700"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -win $_nWave2
srcHBSelect "tb_tensor_core.u_tensor_core_top" -win $_nTrace1
srcSetScope "tb_tensor_core.u_tensor_core_top" -delim "." -win $_nTrace1
srcHBSelect "tb_tensor_core.u_tensor_core_top" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "tb_tensor_core.u_tensor_core_top" -win $_nTrace1
srcHBSelect "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm" -win $_nTrace1
srcSetScope "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm" -delim "." -win \
           $_nTrace1
srcHBSelect "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm" -win $_nTrace1
srcHBSelect "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\]" -win \
           $_nTrace1
srcSetScope "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\]" \
           -delim "." -win $_nTrace1
srcHBSelect "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\]" -win \
           $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\]" \
           -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "A_in       \[3\]" -line 45 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -delim "." -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[1\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[1\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[1\]" \
           -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[0\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[0\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[0\]" \
           -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[0\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[0\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[0\]" \
           -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_a" -line 30 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_b" -line 31 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[1\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[1\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[1\]" \
           -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_a" -line 30 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_b" -line 31 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[2\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[2\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[2\]" \
           -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_a" -line 30 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_b" -line 31 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[3\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[3\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[3\]" \
           -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_a" -line 30 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "operand_b" -line 31 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "result" -line 17 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectGroup -win $_nWave2 {G2}
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 9 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G1" 8)}
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[3\]" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[3\]" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[3\]" \
           -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
wvSelectSignal -win $_nWave2 {( "G1" 1 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 1 2 3 4 5 6 7 8 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G1" 0)}
debReload
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_mul\[0\]" \
           -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma.u_fp16_add_s1" \
           -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -win $_nTrace1
srcSetScope \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "tb_tensor_core.u_tensor_core_top.u_tensor_core_gemm.rowC\[0\].colC\[0\].u_tensor_core_mma" \
           -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "final_add_result" -line 84 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "add_result    \[0\]" -line 82 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "add_result    \[1\]" -line 83 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "mul_result    \[0\]" -line 65 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "mul_result    \[1\]" -line 66 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "mul_result    \[2\]" -line 65 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "mul_result    \[3\]" -line 66 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "A_in       \[0\]" -line 46 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "A_in       \[1\]" -line 46 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "A_in       \[2\]" -line 46 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "A_in       \[3\]" -line 46 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "B_in       \[0\]" -line 47 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "B_in       \[1\]" -line 47 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "B_in       \[2\]" -line 47 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "B_in       \[3\]" -line 47 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "final_add_result" -line 100 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
debExit
