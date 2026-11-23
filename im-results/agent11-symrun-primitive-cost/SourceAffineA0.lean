import SourceCostModel

/-!
Experimental universal *source-direct* primitive-cost lemma for the first
Cryptids SymRun Rule-A fixed block. Unlike the independent JS symbolic
certificate, `costIter` and `stateA0` here are imported original Lean
source definitions. Status pending original-source CI.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0

open BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BB6.Agent11.SourceAffineA0

theorem a0_f424_affine (k d : Nat) (R_tail : List SymTok) :
    costIter true 46 (stateA0 (k+1) (d+6) R_tail) = 32*k + 314 := by
  simp [costIter, costPure, costPureBB, costPureDL, costPureCB,
    costElemBB, costElemDL, costElemCB, costElemCBRun0, fcost,
    stepPure, stepPureBB, stepPureDL, stepPureCB,
    stepElemBB, stepElemDL, stepElemCB, stepElemCB_run0,
    peelPureTok, stripPrefixSym, strictNat, strictList,
    bumpSymL, bumpSymR, prependZeroSym,
    stateA0]
  omega

theorem a0_f412_affine (k d : Nat) (R_tail : List SymTok) :
    costIter false 46 (stateA0 (k+1) (d+6) R_tail) = 28*k + 284 := by
  simp [costIter, costPure, costPureBB, costPureDL, costPureCB,
    costElemBB, costElemDL, costElemCB, costElemCBRun0, fcost,
    stepPure, stepPureBB, stepPureDL, stepPureCB,
    stepElemBB, stepElemDL, stepElemCB, stepElemCB_run0,
    peelPureTok, stripPrefixSym, strictNat, strictList,
    bumpSymL, bumpSymR, prependZeroSym,
    stateA0]
  omega

#print axioms a0_f424_affine
#print axioms a0_f412_affine

end BB6.Agent11.SourceAffineA0
