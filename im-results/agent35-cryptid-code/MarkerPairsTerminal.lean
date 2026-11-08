import Lean.Elab.Tactic.Omega
import CryptidPairs
import A1100

namespace BB6.Agent35PairTerminal
open CryptidBoundary
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Reverse sweep over alternating left stack, with the head scanning one. -/
def back (n : Nat) (L ys : List Bool) : Cfg :=
    ⟨oppairs n ++ L,true,true::ys,0⟩

/-- Four original six-state primitive moves consume one left alternating pair. -/
theorem back_four (n : Nat) (L ys : List Bool) :
    run 4 (back (n+1) L ys) =
       back n L ([true,false] ++ ys) := by
  simp [back,oppairs,run,step,goL,goR,List.append_assoc]

private theorem pairs_snoc (n : Nat) :
    pairs n ++ [true,false] = [true,false] ++ pairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [pairs,List.append_assoc] using
      congrArg (fun zs : List Bool => [true,false] ++ zs) ih

/-- Unbounded reverse sweep converts every crossed 01 pair into a rightward 10 pair. -/
theorem back_run (n : Nat) (L ys : List Bool) :
    run (4*n) (back n L ys) = back 0 L (pairs n ++ ys) := by
  induction n generalizing ys with
  | zero => rfl
  | succ n ih =>
    have ht : 4*(n+1)=4+4*n := by omega
    rw [ht,run_add,back_four,ih]
    simp only [pairs,List.append_assoc]
    rw [pairs_snoc]

/-- Initial constant-size A turn places all remaining pairs in the proven forward scanner. -/
theorem front_seven (m j : Nat) (ys : List Bool) :
    run 7
      (aBoundary m
        ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ ys)))) =
    scanStart j
      (oppairs 1 ++ (pairs (m+1) ++ [true,true]))
      ([true,true,true] ++ ys) := by
  simp [aBoundary,scanStart,oppairs,run,step,goL,goR,pairs,List.append_assoc]

private theorem oppairs_snoc (n : Nat) :
    oppairs n ++ [false,true] = oppairs (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [oppairs,List.append_assoc] using
      congrArg (fun zs : List Bool => [false,true] ++ zs) ih

/-- After scanning, the terminal 111 produces a uniform reversible left stack. -/
theorem turn_two (m j : Nat) (ys : List Bool) :
    run 2
      (⟨oppairs j ++ (oppairs 1 ++ (pairs (m+1) ++ [true,true])),
        false,[true,true,true] ++ ys,0⟩ : Cfg) =
    back (j+2) (pairs (m+1) ++ [true,true]) ys := by
  simp only [back,run,step,goR,goL]
  congr 1
  rw [show oppairs (j+2) = (oppairs j ++ [false,true]) ++ [false,true] by
    rw [oppairs_snoc,oppairs_snoc]]
  simp [oppairs,List.append_assoc]

/-- Terminal left-stack pair and the initial right one enter the source D sweep. -/
theorem back_base (m j : Nat) (ys : List Bool) :
    run 4
      (back 0 (pairs (m+1) ++ [true,true]) (pairs (j+2) ++ ys)) =
    sweepD m ([true,true,false] ++ (pairs (j+2) ++ ys)) := by
  simp [back,sweepD,pairs,run,step,goL,goR,List.append_assoc]

/-- Arbitrarily many alternating terminal pairs, exactly 6 primitive moves per pair. -/
theorem a_many_front (m j : Nat) (ys : List Bool) :
    run (6*j+21)
      (aBoundary m
        ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ ys)))) =
    sweepD m ([true,true,false] ++ (pairs (j+2) ++ ys)) := by
  have ht : 6*j+21=7+(2*j+(2+(4*(j+2)+4))) := by omega
  rw [ht,run_add,run_add,run_add,run_add,front_seven,scan_run]
  change run 4 (run (4*(j+2))
      (back (j+2) (pairs (m+1) ++ [true,true]) ys)) = _
  rw [back_run]
  exact back_base m j ys

/-- ALL j≥1 original-source A terminal 11(01)^j11, exact primitive runtime. -/
theorem a_many_pairs_return (m j : Nat) (ys : List Bool) :
    run (2*m+6*j+24)
      (aBoundary m
        ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ ys)))) =
    (⟨[],false,
      List.replicate (2*m+5) true ++
        (false :: (pairs (j+2) ++ ys)),5⟩ : Cfg) := by
  have ht : 2*m+6*j+24=(6*j+21)+(2*m+3) := by omega
  rw [ht,run_add,a_many_front,sweepD_run]
  have hn : List.replicate (2*m+3) true ++ [true,true] =
      List.replicate (2*m+5) true := by
    rw [←List.replicate_append_replicate]
    congr 1
    omega
  simp [List.append_assoc,hn]

#print axioms back_four
#print axioms back_run
#print axioms front_seven
#print axioms turn_two
#print axioms a_many_front
#print axioms a_many_pairs_return
end BB6.Agent35PairTerminal
