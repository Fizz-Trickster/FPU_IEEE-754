verdiSetActWin -dock widgetDock_<Decl._Tree>
simSetSimulator "-vcssv" -exec "simv" -args "-a vcs.log"
debImport "-dbdir" "simv.daidir"
debLoadSimResult \
           /home/ysyoon/PROJECT/FPU_IEEE-754/Accumulation/sim_fp16/waveform.fsdb
wvCreateWindow
verdiWindowResize -win $_Verdi_1 "1810" "610" "900" "700"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "a_fp16" -line 14 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "clk" -line 11 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "a_fp16" -line 14 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "b_fp16" -line 15 -pos 1 -win $_nTrace1
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
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
wvSetRadix -win $_nWave2 -format Bin
srcDeselectAll -win $_nTrace1
srcSelect -signal "acc_reg" -line 123 -pos 2 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
verdiSetActWin -win $_nWave2
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "a_fixed" -line 109 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 5 )} 
wvSetRadix -win $_nWave2 -format Bin
wvSetPosition -win $_nWave2 {("G2" 0)}
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSelectGroup -win $_nWave2 {G3}
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16.f2i" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "fp16_in" -line 62 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "sign" -line 64 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16.f2i" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "fraction" -line 66 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -win $_nWave2
wvGetSignalOpen -win $_nWave2
wvGetSignalSetScope -win $_nWave2 "/tb_fp_acc"
wvGetSignalSetScope -win $_nWave2 "/tb_fp_acc/u_kulisch_acc_fp16"
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16.f2i" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "exponent" -line 65 -pos 1 -win $_nTrace1
srcAction -pos 64 11 2 -win $_nTrace1 -name "exponent" -ctrlKey off
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "fraction" -line 66 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvUnknownSaveResult -win $_nWave2 -clear
srcDeselectAll -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "a_fp16" -line 109 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -word -line 108 -pos 14 -win $_nTrace1
srcAction -pos 108 14 2 -win $_nTrace1 -name "f2i" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -signal "fp16_in" -line 62 -pos 1 -win $_nTrace1
srcAction -pos 61 11 4 -win $_nTrace1 -name "fp16_in" -ctrlKey off
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvUnknownSaveResult -win $_nWave2 -clear
verdiSetActWin -win $_nWave2
wvGetSignalOpen -win $_nWave2
wvGetSignalSetOptions -win $_nWave2 -all off
wvGetSignalSetSignalFilter -win $_nWave2 "*"
wvGetSignalSetOptions -win $_nWave2 -all on
wvGetSignalSetSignalFilter -win $_nWave2 "*"
wvSetCursor -win $_nWave2 9116.578947 -snap {("G3" 0)}
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
wvGetSignalOpen -win $_nWave2
wvGetSignalSetScope -win $_nWave2 "/tb_fp_acc/u_kulisch_acc_fp16/f2i"
srcDeselectAll -win $_nTrace1
srcSelect -signal "fp16_in" -line 62 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "sign" -line 73 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "exponent" -line 74 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "fraction" -line 75 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
wvSelectSignal -win $_nWave2 {( "G2" 5 )} 
wvSelectSignal -win $_nWave2 {( "G2" 2 3 4 5 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSelectSignal -win $_nWave2 {( "G2" 1 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G3" 0)}
wvSetPosition -win $_nWave2 {("G2" 0)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "fp16_in" -line 62 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "sign" -line 64 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "exponent" -line 65 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "fraction" -line 66 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "mantissa" -line 67 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 2 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvSelectSignal -win $_nWave2 {( "G2" 3 4 )} 
wvSelectSignal -win $_nWave2 {( "G2" 3 4 5 )} 
wvSelectSignal -win $_nWave2 {( "G2" 3 4 5 )} 
wvSetRadix -win $_nWave2 -format Bin
srcDeselectAll -win $_nTrace1
srcSelect -signal "shifted_val" -line 82 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSelectGroup -win $_nWave2 {G3}
verdiSetActWin -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "shift" -line 78 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
verdiSetActWin -win $_nWave2
wvSetRadix -win $_nWave2 -2Com
srcDeselectAll -win $_nTrace1
srcSelect -signal "shifted_val" -line 86 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "shift" -line 86 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 6 )} 
verdiSetActWin -win $_nWave2
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G1" 4)}
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "a_fixed" -line 111 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 5 )} 
wvSetRadix -win $_nWave2 -format Bin
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16.f2i" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16.f2i" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "shifted_val" -line 84 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 6 )} 
wvSetRadix -win $_nWave2 -format Bin
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 2 )} 
wvSelectSignal -win $_nWave2 {( "G2" 1 )} 
wvSelectSignal -win $_nWave2 {( "G2" 1 2 3 4 5 6 7 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 0)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "shifted_val" -line 86 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "shifted_mantissa" -line 86 -pos 1 -win $_nTrace1
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
wvZoomIn -win $_nWave2
wvZoomIn -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 7749.092105 108645.434211
verdiSetActWin -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 2522.408553 69830.889404
wvZoomIn -win $_nWave2
wvZoomOut -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 1 )} 
wvSetRadix -win $_nWave2 -format Bin
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
wvSelectGroup -win $_nWave2 {G2}
wvSelectSignal -win $_nWave2 {( "G2" 1 )} 
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "shift" -line 93 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "fixed_val" -line 96 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvSetRadix -win $_nWave2 -format Bin
wvSelectSignal -win $_nWave2 {( "G2" 2 )} 
wvSetRadix -win $_nWave2 -2Com
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "f2i" -line 102 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "fixed_val" -line 96 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectGroup -win $_nWave2 {G3}
wvSelectSignal -win $_nWave2 {( "G2" 5 )} 
verdiSetActWin -win $_nWave2
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G3" 0)}
wvSetPosition -win $_nWave2 {("G2" 4)}
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G3" 0)}
wvSetPosition -win $_nWave2 {("G2" 3)}
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "exponent" -line 81 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSetPosition -win $_nWave2 {("G2" 0)}
verdiSetActWin -win $_nWave2
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G2" 0)}
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G2" 1)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "shift" -line 83 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 2 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 2)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvSetRadix -win $_nWave2 -format UDec
wvSetRadix -win $_nWave2 -Unsigned
wvSetRadix -win $_nWave2 -2Com
wvSetRadix -win $_nWave2 -Unsigned
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvSetRadix -win $_nWave2 -format Bin
wvSetRadix -win $_nWave2 -2Com
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvSetRadix -win $_nWave2 -format UDec
wvSetRadix -win $_nWave2 -Unsigned
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvSetRadix -win $_nWave2 -format Bin
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
wvSelectSignal -win $_nWave2 {( "G2" 3 )} 
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
debReload
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
wvSetRadix -win $_nWave2 -format Bin
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 51322.716649 77803.290036
wvDisplayGridCount -win $_nWave2 -off
wvGetSignalClose -win $_nWave2
wvReloadFile -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 4 )} 
wvSelectGroup -win $_nWave2 {G3}
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
srcSetScope "tb_fp_acc.u_kulisch_acc_fp16" -delim "." -win $_nTrace1
srcHBSelect "tb_fp_acc.u_kulisch_acc_fp16" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
debReload
srcDeselectAll -win $_nTrace1
srcSelect -signal "o_kulisch_acc" -line 18 -pos 1 -win $_nTrace1
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
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 9804.973684 25777.592105
verdiSetActWin -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvSetPosition -win $_nWave2 {("G1" 1)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "rst_n" -line 12 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvZoom -win $_nWave2 10121.263158 56932.105263
verdiSetActWin -win $_nWave2
debReload
wvSetPosition -win $_nWave2 {("G2" 0)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "i_fp_data" -line 14 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "i_init_acc" -line 15 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "i_init" -line 16 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "o_kulisch_acc" -line 18 -pos 1 -win $_nTrace1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 5 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G2" 1 )} 
wvSelectGroup -win $_nWave2 {G2}
wvSelectSignal -win $_nWave2 {( "G2" 1 )} 
wvSelectSignal -win $_nWave2 {( "G2" 1 2 3 )} 
wvSelectSignal -win $_nWave2 {( "G2" 1 2 3 4 )} 
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
wvSelectSignal -win $_nWave2 {( "G1" 3 )} 
wvSelectSignal -win $_nWave2 {( "G1" 3 4 5 6 )} 
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G5" 0)}
wvAddGroup -win $_nWave2 {G5}
wvSetCursor -win $_nWave2 14756.152459 -snap {("G4" 0)}
wvSelectSignal -win $_nWave2 {( "G3" 1 )} 
wvSelectGroup -win $_nWave2 {G4}
wvSelectSignal -win $_nWave2 {( "G1" 3 )} 
wvSelectSignal -win $_nWave2 {( "G1" 3 4 5 )} 
wvSelectSignal -win $_nWave2 {( "G1" 3 4 5 6 )} 
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G5" 0)}
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G5" 4)}
wvSelectGroup -win $_nWave2 {G4}
wvSelectSignal -win $_nWave2 {( "G5" 3 4 )} 
wvSelectSignal -win $_nWave2 {( "G5" 3 )} 
wvSetPosition -win $_nWave2 {("G5" 3)}
wvSetPosition -win $_nWave2 {("G5" 2)}
wvSetPosition -win $_nWave2 {("G5" 1)}
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G5" 1)}
wvSetPosition -win $_nWave2 {("G5" 2)}
wvSelectSignal -win $_nWave2 {( "G5" 1 )} 
wvSetPosition -win $_nWave2 {("G5" 1)}
wvSetPosition -win $_nWave2 {("G5" 3)}
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G5" 3)}
debReload
debReload
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomIn -win $_nWave2
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
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 6772.315789 109600.947368
wvZoom -win $_nWave2 12319.649861 39785.718560
debReload
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 11528.520941 25984.346572
wvZoomOut -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G5" 4 )} 
wvSelectSignal -win $_nWave2 {( "G5" 4 )} 
wvSetRadix -win $_nWave2 -format Bin
wvZoom -win $_nWave2 13506.686553 24624.357713
wvSelectSignal -win $_nWave2 {( "G5" 3 )} 
wvSelectSignal -win $_nWave2 {( "G5" 3 )} 
wvSetRadix -win $_nWave2 -format Bin
wvSelectSignal -win $_nWave2 {( "G3" 1 )} 
wvSelectSignal -win $_nWave2 {( "G5" 3 )} 
wvSetCursor -win $_nWave2 28424.114402 -snap {("G2" 3)}
wvSelectSignal -win $_nWave2 {( "G2" 2 )} 
wvSelectSignal -win $_nWave2 {( "G3" 1 )} 
wvSelectSignal -win $_nWave2 {( "G3" 1 )} 
wvSetRadix -win $_nWave2 -format Hex
srcDeselectAll -win $_nTrace1
srcSelect -signal "fixed_data" -line 112 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcAddSelectedToWave -clipboard -win $_nTrace1
wvDrop -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 2)}
wvSetPosition -win $_nWave2 {("G2" 3)}
wvSetPosition -win $_nWave2 {("G2" 4)}
wvSetPosition -win $_nWave2 {("G3" 0)}
verdiSetActWin -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 4)}
wvMoveSelected -win $_nWave2
wvSetPosition -win $_nWave2 {("G2" 5)}
wvSelectSignal -win $_nWave2 {( "G2" 5 )} 
wvSetRadix -win $_nWave2 -format Bin
