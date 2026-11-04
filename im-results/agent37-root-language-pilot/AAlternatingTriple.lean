import Lean.Elab.Tactic.Omega
import CryptidTriplePairs
import A1100

namespace BB6.Agent37AAlternatingTriple

open CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The exact left tape after the initial seven-step A/110 turn. -/
def leftCore (m : Nat) : List Bool :=
  [false,true,true,false] ++ pairs m ++ [true,true]

def startA (m r : Nat) (ys : List Bool) : Cfg :=
  aBoundary m ([true,true,false] ++ pairs r ++ ([true,true,true] ++ ys))

theorem start7 (m r : Nat) (ys : List Bool) :
    run 7 (startA m r ys) =
      scanStart r (leftCore m) ([true,true,true] ++ ys) := by
  simp [startA, aBoundary, leftCore, scanStart,
    run, step, goL, goR, pairs, List.append_assoc]

/-- Three-one terminal becomes a B/0 return from any reverse-pair stack. -/
theorem triple8 (m r : Nat) (ys : List Bool) :
    run 8
      (⟨oppairs r ++ leftCore m, false, [true,true,true] ++ ys, 0⟩ : Cfg) =
      bPop r (leftCore m) ([false,true,false] ++ ys) := by
  simpa [bPop] using
    (aTriple8 (oppairs r ++ leftCore m) ys)

/-- The B-pop output grows exactly one 01 pair. -/
theorem bPop_right (r : Nat) (ys : List Bool) :
    oppairs r ++ ([false,true,false] ++ ys) =
      oppairs (r+1) ++ (false :: ys) := by
  calc
    _ = (oppairs r ++ [false,true]) ++ (false::ys) := by
      simp [List.append_assoc]
    _ = ([false,true] ++ oppairs r) ++ (false::ys) := by
      rw [oppairs_comm_one]
    _ = _ := by simp [oppairs]

/-- Universal six-step closing move after the B-pop stage, with all
    parameters and all untouched right suffixes symbolic. -/
theorem close6 (m r : Nat) (ys : List Bool) :
    run 6
      (⟨leftCore m, false, oppairs (r+1) ++ (false::ys), 1⟩ : Cfg) =
      sweepD m ([true,true] ++ oppairs (r+2) ++ (false::ys)) := by
  simp [leftCore, sweepD, oppairs, pairs,
    run, step, goL, goR, List.append_assoc]

/-- First 6r+21 actions of the entire 110 (10)^r 111 A-language,
    with the remaining m-deep D sweep left intact. -/
theorem front (m r : Nat) (ys : List Bool) :
    run (6*r+21) (startA m r ys) =
      sweepD m ([true,true] ++ oppairs (r+2) ++ (false::ys)) := by
  have ht : 6*r+21 = 7+(2*r+(8+(4*r+6))) := by omega
  rw [ht, run_add, run_add, run_add, run_add, start7, scan_run, triple8]
  rw [bPop_run,bPop_right]
  exact close6 m r ys

/-- Uniform original six-state A boundary return, subsuming separately
    established 110111, 11010111 and 1101010111 terminals.
    No restriction on m, r or the physical suffix. -/
theorem a_all_alternating_triple (m r : Nat) (ys : List Bool) :
    run (2*m+6*r+24) (startA m r ys) =
      ⟨[],false,List.replicate (2*m+5) true ++
        (oppairs (r+2) ++ (false::ys)),5⟩ := by
  have ht : 2*m+6*r+24 = (6*r+21)+(2*m+3) := by omega
  rw [ht, run_add, front, sweepD_run]
  have hp : List.replicate (2*m+3) true ++
       ([true,true] ++ oppairs (r+2) ++ (false::ys)) =
      List.replicate (2*m+5) true ++
        (oppairs (r+2) ++ (false::ys)) := by
    calc
      _ = (List.replicate (2*m+3) true ++ List.replicate 2 true) ++
           (oppairs (r+2) ++ (false::ys)) := by
             simp [List.append_assoc]
      _ = List.replicate ((2*m+3)+2) true ++
           (oppairs (r+2) ++ (false::ys)) := by
             rw [List.replicate_append_replicate]
      _ = _ := by rw [show 2*m+3+2=2*m+5 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hp

/-- Original raw F/0 input with any number of alternating pairs preceding
    three ones. Exact primitive time and entire arbitrary output suffix. -/
theorem full_A_alternating_triple (k r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+6*r+62)
      (init (List.replicate (3*k+1) true ++
        false :: ([true,true,false] ++ pairs r ++ ([true,true,true] ++ ys)))) =
      ⟨[],false,List.replicate (8*k+11) true ++
        (oppairs (r+2) ++ (false::ys)),5⟩ := by
  have ht : 12*k*k+49*k+6*r+62 =
     (12*k*k+41*k+32)+(2*(4*k+3)+6*r+24) := by omega
  rw [ht, run_add, prefix_A]
  change run (2*(4*k+3)+6*r+24)
    (startA (4*k+3) r ys) = _
  rw [a_all_alternating_triple]
  rw [show 2*(4*k+3)+5 = 8*k+11 by omega]

#print axioms start7
#print axioms triple8
#print axioms bPop_right
#print axioms close6
#print axioms front
#print axioms a_all_alternating_triple
#print axioms full_A_alternating_triple

end BB6.Agent37AAlternatingTriple
