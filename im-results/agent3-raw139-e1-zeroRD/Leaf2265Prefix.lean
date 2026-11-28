import Leaf2265MacroRounds

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
A source-derived finite prefix of the astronomically late E0 query.
This is a compiler-preflight for the complete 435-section certificate,
not a bound or halting proof by itself.
-/

theorem prefixSix : Runs 109848 blankCfg
    (S 279 (pre [true,true,false,true] blank)) := by
  have h0 : Runs 93 (S 3 blank)
      (S 7 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre] using zeroOddRound 1 blank
  have h1 : Runs 413
      (S 7 (pre [false,false,false,true,false,true] blank))
      (S 17 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre] using zeroOddRound 3
      (pre [true,false,true] blank)
  have h2 : Runs 2263
      (S 17 (pre [false,false,false,true,false,true,true,false,true] blank))
      (S 42 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre] using zeroOddRound 8
      (pre [true,false,true,true,false,true] blank)
  have h3 : Runs 13663
      (S 42 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank))
      (S 108 (pre [true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre] using zeroEvenRound 20
      (pre [true,false,true,true,false,true,true,false,true] blank)
  have h4 : Runs 434
      (S 108 (pre [true,false,true,true,false,true,true,false,true] blank))
      (S 109 (pre [false,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre] using one 108
      (pre [false,true,true,false,true,true,false,true] blank)
  have h5 : Runs 92969
      (S 109 (pre [false,false,true,true,false,true,true,false,true] blank))
      (S 279 (pre [true,true,false,true] blank)) := by
    simpa [pre] using twoOddZeroRound 54
      (pre [true,true,false,true] blank)
  have h := chain seed (chain h0 (chain h1 (chain h2 (chain h3 (chain h4 h5)))))
  simpa only [Nat.reduceAdd] using h

#print axioms prefixSix
end BB6.Agent3Leaf2265
