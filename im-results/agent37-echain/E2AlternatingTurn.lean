import Lean.Elab.Tactic.Omega
import CryptidPairs

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2AlternatingTurn
open CryptidBoundary

/-- The A/0 frontier grammar 11(01)^r00Y, for r>=1. -/
def aFront (r : Nat) : List Bool :=
  [true,true] ++ (oppairs r ++ [false,false])

def aStart (r : Nat) (L ys : List Bool) : Cfg :=
  ⟨L,false,aFront r ++ ys,0⟩

def aScan (i r : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs i ++ (true::L),false,
    true :: (oppairs r ++ ([false,false] ++ ys)),0⟩

private theorem aStartFive (r : Nat) (L ys : List Bool) :
    run 5 (aStart (r+1) L ys) = aScan 0 (r+1) L ys := by
  simp [aStart,aFront,aScan,run,step,goL,goR,oppairs,
    List.append_assoc]

private theorem aScanTwo (i r : Nat) (L ys : List Bool) :
    run 2 (aScan i (r+1) L ys) = aScan (i+1) r L ys := by
  simp [aScan,run,step,goL,goR,oppairs,List.append_assoc]

private theorem aScanRun (i r : Nat) (L ys : List Bool) :
    run (2*r) (aScan i r L ys) = aScan (r+i) 0 L ys := by
  induction r generalizing i with
  | zero => simp [run]
  | succ r ih =>
      have ht : 2*(r+1)=2+2*r := by omega
      rw [ht,run_add,aScanTwo,ih (i+1)]
      congr 1
      omega

/-- Exact finite A/0-to-D/0 turn on 100Y, preserving the arbitrary
    left stack, whose initial symbolic prefix is (01)^r 1. -/
private theorem aHundredFive (r : Nat) (L ys : List Bool) :
    run 5 (⟨oppairs r ++ (true::L),false,
      [true,false,false] ++ ys,0⟩ : Cfg) =
    ⟨true :: (oppairs r ++ (true::L)),false,
      [true,true] ++ ys,3⟩ := by
  simp [run,step,goL,goR,List.append_assoc]

private def dShort (r : Nat) (L ys : List Bool) : Cfg :=
  ⟨true :: (oppairs r ++ (true::L)),false,
    [true,true] ++ ys,3⟩

private theorem dShortTwo (r : Nat) (L ys : List Bool) :
    run 2 (dShort (r+1) L ys) =
      dShort r L ([true,true] ++ ys) := by
  simp [dShort,run,step,goL,goR,oppairs,
    List.append_assoc]

private theorem dShortBase (L ys : List Bool) :
    run 2 (dShort 0 L ys) =
      ⟨L,true,List.replicate 4 true ++ ys,3⟩ := by
  simp [dShort,run,step,goL,goR,oppairs]

private theorem dShortRun (r : Nat) (L ys : List Bool) :
    run (2*(r+1)) (dShort r L ys) =
      ⟨L,true,List.replicate (2*r+4) true ++ ys,3⟩ := by
  induction r generalizing ys with
  | zero => exact dShortBase L ys
  | succ r ih =>
      have ht : 2*(r+1+1)=2+2*(r+1) := by omega
      rw [ht,run_add,dShortTwo,ih]
      have hrep : List.replicate (2*r+4) true ++ ([true,true] ++ ys) =
          List.replicate (2*(r+1)+4) true ++ ys := by
        calc
          _ = (List.replicate (2*r+4) true ++ List.replicate 2 true) ++ ys := by
            simp [List.append_assoc]
          _ = List.replicate ((2*r+4)+2) true ++ ys := by
            rw [List.replicate_append_replicate]
          _ = _ := by rw [show (2*r+4)+2=2*(r+1)+4 by omega]
      exact congrArg (fun z : List Bool => Cfg.mk L true z 3) hrep

/-- The 100Y local turn is unbounded in the unknown alternating left
    stack and returns in exactly 2r+7 primitive steps. -/
theorem aHundredRun (r : Nat) (L ys : List Bool) :
    run (2*r+7)
      (⟨oppairs r ++ (true::L),false,
        [true,false,false] ++ ys,0⟩ : Cfg) =
    ⟨L,true,List.replicate (2*r+4) true ++ ys,3⟩ := by
  have ht : 2*r+7=5+2*(r+1) := by omega
  rw [ht,run_add,aHundredFive]
  exact dShortRun r L ys

/-- For every positive length of the terminating 01 stack, an A/0 turn
    11(01)^r00Y -> D/1 with 2r+4 consecutive ones, preserving unknown
    left context and right tail. This extends the r=1 16-step lemma to
    an unbounded second independent stack parameter. -/
theorem aTurnAll (r : Nat) (L ys : List Bool) :
    run (4*(r+1)+12) (aStart (r+1) L ys) =
    ⟨L,true,List.replicate (2*(r+1)+4) true ++ ys,3⟩ := by
  have ht : 4*(r+1)+12 =
      5+(2*(r+1)+(2*(r+1)+7)) := by omega
  rw [ht,run_add,aStartFive]
  rw [run_add,aScanRun]
  change run (2*(r+1)+7)
    (⟨oppairs (r+1) ++ (true::L),false,
      [true,false,false] ++ ys,0⟩ : Cfg) = _
  exact aHundredRun (r+1) L ys

/-- The zero-alternating-pair base has the same A->D shape. -/
private theorem aTurnZero (L ys : List Bool) :
    run 12 (aStart 0 L ys) =
    ⟨L,true,List.replicate 4 true ++ ys,3⟩ := by
  simp [aStart,aFront,run,step,goL,goR,oppairs,List.append_assoc]

/-- The universal 11(01)^r00 -> D1 turn actually holds for *every* r>=0.
    The r=0 base is a separate direct twelve-step local path. -/
theorem aTurnAllNat (r : Nat) (L ys : List Bool) :
    run (4*r+12) (aStart r L ys) =
    ⟨L,true,List.replicate (2*r+4) true ++ ys,3⟩ := by
  cases r with
  | zero => exact aTurnZero L ys
  | succ r =>
      simpa [Nat.succ_eq_add_one] using aTurnAll r L ys

#print axioms aHundredRun
#print axioms aTurnAll
#print axioms aTurnAllNat

end BB6.Agent37E2AlternatingTurn
