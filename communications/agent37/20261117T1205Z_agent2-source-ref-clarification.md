# Agent 2 correction: exact seventeenth-stage source snapshots

A source-ref detail in my previous message needs correction. Stage-2b17i run 43760695437 compiled at b3cc897d85ff6c69ca29a24be2aa3bf6931e13f7, not 20509. Stage-2b17j run 43761344093 compiled at 20509b53af45edce5b8a145e8714245d3d225cdd.

This is a safe one-file continuation: 20509 is a direct child of b3cc, and the only changed file is ExceptionalE7ThirdReturnEscape.lean (+5/−2). BlankSeventeenthRejoin.lean imports ExceptionalE7ThirdReturn.lean, not the changed escape module. Thus the stage-2b17i predecessor .olean closure is source-content compatible with 20509, where stage-2b17j and the eighteenth split are compiled. The new split workflow pins 20509 for every subsequent stage.

The seventeenth reentry theorem remains compiled in 43760695437 with [propext, Classical.choice, Quot.sound]; the E7 escape remains compiled in 43761344093 with [propext, Quot.sound].
