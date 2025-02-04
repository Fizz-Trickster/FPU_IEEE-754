verdiSetActWin -dock widgetDock_<Decl._Tree>
simSetSimulator "-vcssv" -exec "simv" -args "-a vcs.log"
debImport "-dbdir" "simv.daidir"
debLoadSimResult \
           /home/ysyoon/PROJECT/FPU_IEEE-754/Addition_and_Subtraction/sim_fp16/waveform.fsdb
wvCreateWindow
verdiWindowResize -win $_Verdi_1 "1721" "170" "1718" "1368"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
debReload
srcHBSelect "tb_fp_add.u_fp16_add" -win $_nTrace1
srcSetScope "tb_fp_add.u_fp16_add" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_add.u_fp16_add" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "a_operand" -line 10 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "b_operand" -line 11 -pos 1 -win $_nTrace1
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
srcDeselectAll -win $_nTrace1
srcSelect -signal "b_operand" -line 11 -pos 1 -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "result" -line 12 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
wvSelectSignal -win $_nWave2 {( "G1" 1 )} 
wvSelectSignal -win $_nWave2 {( "G1" 1 2 )} 
wvSelectSignal -win $_nWave2 {( "G1" 1 2 3 )} 
wvSelectSignal -win $_nWave2 {( "G1" 1 2 3 )} 
wvSetRadix -win $_nWave2 -format Bin
srcHBSelect "tb_fp_add" -win $_nTrace1
srcSetScope "tb_fp_add" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_add" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "tb_fp_add.u_fp16_add" -win $_nTrace1
srcSetScope "tb_fp_add.u_fp16_add" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_add.u_fp16_add" -win $_nTrace1
wvSetCursor -win $_nWave2 3670.227163 -snap {("G2" 0)}
verdiSetActWin -win $_nWave2
wvSelectGroup -win $_nWave2 {G2}
wvSetPosition -win $_nWave2 {("G2" 0)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "isSpecialCase" -line 57 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSetCursor -win $_nWave2 13886.487187 -snap {("G1" 3)}
verdiSetActWin -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "isNaNA" -line 61 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "isNaNB" -line 61 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
debReload
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 2 )} 
wvSelectSignal -win $_nWave2 {( "G2" 2 3 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 1)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "expA" -line 108 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "expDiff" -line 102 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSetPosition -win $_nWave2 {("G3" 0)}
verdiSetActWin -win $_nWave2
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G3" 1)}
wvSetPosition -win $_nWave2 {("G3" 1)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "alignA" -line 112 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "alignB" -line 113 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G3" 2 )} 
wvSelectSignal -win $_nWave2 {( "G3" 2 3 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G3" 2 3 )} 
wvSetRadix -win $_nWave2 -format Bin
wvSelectSignal -win $_nWave2 {( "G3" 2 3 )} 
wvSetRadix -win $_nWave2 -format Bin
debReload
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "alignA" -line 104 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "alignB" -line 104 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G3" 2 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G3" 2 3 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G3" 3)}
wvSelectSignal -win $_nWave2 {( "G3" 2 )} 
wvSelectSignal -win $_nWave2 {( "G3" 2 3 )} 
wvSelectSignal -win $_nWave2 {( "G3" 2 3 )} 
wvSetRadix -win $_nWave2 -format Bin
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "sum_mant" -line 124 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "mantFinal" -line 150 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectGroup -win $_nWave2 {G4}
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G3" 5 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G4" 0)}
wvSetPosition -win $_nWave2 {("G3" 4)}
wvSetPosition -win $_nWave2 {("G4" 0)}
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "mantFinal" -line 150 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSelectSignal -win $_nWave2 {( "G3" 4 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G3" 4 )} 
wvSetRadix -win $_nWave2 -format Bin
srcDeselectAll -win $_nTrace1
srcSelect -signal "sum_mant\[MWIDTH+1+RWIDTH\]" -line 156 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectGroup -win $_nWave2 {G5}
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G4" 2 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G5" 0)}
wvSetPosition -win $_nWave2 {("G4" 1)}
wvSelectSignal -win $_nWave2 {( "G3" 4 )} 
wvSelectSignal -win $_nWave2 {( "G3" 4 )} 
wvSetRadix -win $_nWave2 -format Hex
srcDeselectAll -win $_nTrace1
srcSelect -signal "sum_mant\[MWIDTH+1+RWIDTH\]" -line 156 -pos 1 -partailSelPos \
          12 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "sum_mant\[MWIDTH+1+RWIDTH\]" -line 156 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "mantFinal" -line 164 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "sum_mant" -line 164 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
debReload
wvSelectSignal -win $_nWave2 {( "G4" 4 )} 
verdiSetActWin -win $_nWave2
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G5" 0)}
wvSetPosition -win $_nWave2 {("G4" 3)}
wvSelectSignal -win $_nWave2 {( "G4" 3 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G5" 0)}
wvSetPosition -win $_nWave2 {("G4" 2)}
wvSelectSignal -win $_nWave2 {( "G4" 2 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G5" 0)}
wvSetPosition -win $_nWave2 {("G4" 1)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "expFinal" -line 165 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
debReload
verdiSetActWin -win $_nWave2
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
wvSetCursor -win $_nWave2 217674.395448 -snap {("G4" 0)}
