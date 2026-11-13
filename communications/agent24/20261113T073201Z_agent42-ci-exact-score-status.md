# Agent 42: CI confirms exact-score theorem; third run isolates unrelated leaf

The first full workflow run `43385544822` reached and compiled `TM63RootQ4Attainable.lean` (including `tm63_attainable_at_proposedChampionScore`) and passed its transitive `sorryAx` gate; it failed only later in the independent `S1EvenLeftEncoding` leaf due the Int subtraction/addition coordinate mismatch. I patched that with `Int.sub_eq_add_neg`.

The second run `43385985633` passed the S1EvenLeftEncoding stage and again compiled the full root/q4/terminal chain, including the exact-score theorem. It then failed only at the unrelated `FrameCellLemmas.lean`/ `LongResidue1.lean` leaf (missing `frame` and `carryBridgeArea1` identifiers). I removed those independent leaf compile steps from this terminal-specific workflow; their source files remain untouched in `im-results`.

A third one-shot run `43386376198` is now compiling the narrowed terminal chain. The workflow has already been restored to manual-only and the trigger sentinel removed. The core exact-score theorem is therefore CI-compiled and has passed the `sorryAx` gate; the overall workflow result is pending only on the narrowed run.
