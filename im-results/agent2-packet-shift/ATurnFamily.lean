import Lean.Elab.Tactic.Omega
import CryptidTriplePairs
import EGenericTurn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent2ATurnFamily
open CryptidBoundary

def front (r : Nat) : List Bool :=
  [true,true] ++ (oppairs r ++ [true,true])

def aStart (r : Nat) (L ys : List Bool) : Cfg :=
  ⟨L,false,front r ++ ys,0⟩

def aScan (i r : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs i ++ (true::L),false,
    true :: (oppairs r ++ ([true,true] ++ ys)),0⟩

private theorem aStart_five (r : Nat) (L ys : List Bool) :
    run 5 (aStart (r+1) L ys) = aScan 0 (r+1) L ys := by
  simp [aStart,front,aScan,run,step,goL,goR,oppairs,List.append_assoc]

private theorem aScan_two (i r : Nat) (L ys : List Bool) :
    run 2 (aScan i (r+1) L ys) =
      aScan (i+1) r L ys := by
  simp [aScan,run,step,goL,goR,oppairs,List.append_assoc]

private theorem aScan_run (i r : Nat) (L ys : List Bool) :
    run (2*r) (aScan i r L ys) = aScan (r+i) 0 L ys := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
      have ht : 2*(r+1) = 2+2*r := by omega
      rw [ht,run_add,aScan_two,ih (i+1)]
      have heq : r+(i+1) = (r+1)+i := by omega
      rw [heq]

private theorem alternating (n : Nat) (ys : List Bool) :
    true :: (oppairs n ++ ([false,true,false] ++ ys)) =
    pairs (n+2) ++ ys := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [oppairs, pairs, List.cons_append]
      simpa [pairs] using congrArg (fun z : List Bool => true::false::z) ih

/-- Literal six-state A turn for EVERY positive r and arbitrary unknown
    left tape and right suffix; it is an unbounded source-inductive result. -/
theorem a_turn_all (r : Nat) (L ys : List Bool) :
    run (6*(r+1)+14) (aStart (r+1) L ys) =
      ⟨L,true,pairs (r+3) ++ ys,2⟩ := by
  let n := r+1
  have ht : 6*(r+1)+14 = 5+(2*n+(8+(4*n+1))) := by
    dsimp [n]
    omega
  rw [ht,run_add,aStart_five]
  rw [run_add,aScan_run]
  rw [run_add]
  change run (4*n+1)
    (run 8 (⟨oppairs n ++ (true::L),false,[true,true,true] ++ ys,0⟩ : Cfg)) = _
  rw [aTriple8]
  rw [run_add]
  change run 1
    (run (4*n) (bPop n (true::L) ([false,true,false] ++ ys))) = _
  rw [bPop_run]
  change run 1
    (⟨true::L,false,oppairs n ++ ([false,true,false] ++ ys),1⟩ : Cfg) = _
  simp only [run,step,goL,goR]
  simpa [n] using alternating (r+1) ys

/-- Every positive alternating 01-stack between the two 11 termini
    gives a parameter-unbounded original-source E return. -/
theorem full_E_alternating_family (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+6*(r+1)+62+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (front (r+1) ++ ys)))) =
      ⟨[],false,List.replicate (8*k+3) true ++
        BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys,5⟩ := by
  have ht : 12*k*k+49*k+6*(r+1)+62+4*q =
    12*k*k+49*k+(6*(r+1)+14)+48+4*q := by omega
  rw [ht]
  apply BB6.Agent2EGenericTurn.full_E_from_turn
  intro L
  simpa [aStart] using a_turn_all r L ys

#print axioms aStart_five
#print axioms aScan_two
#print axioms aScan_run
#print axioms a_turn_all
#print axioms full_E_alternating_family
end BB6.Agent2ATurnFamily
