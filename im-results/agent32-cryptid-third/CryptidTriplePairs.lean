import Lean.Elab.Tactic.Omega
import CryptidSix

set_option maxHeartbeats 8000000
namespace CryptidBoundary

/-- A universal 8-step A/B handoff, uniform in the entire unknown left tape. -/
theorem aTriple8 (L ys : List Bool) :
  run 8 (⟨L, false, [true,true,true] ++ ys, 0⟩ : Cfg) =
    ⟨L, false, [false,true,false] ++ ys, 1⟩ := by
  cases L with
  | nil => simp [run, step, goL, goR]
  | cons a as =>
    cases a <;> simp [run, step, goL, goR]

def bPop (q : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs q ++ L, false, ys, 1⟩

theorem bPop_step (q : Nat) (L ys : List Bool) :
  run 4 (bPop (q+1) L ys) = bPop q L (false::true::ys) := by
  simp [bPop, oppairs, run, step, goL, goR]

theorem bPop_run (q : Nat) (L ys : List Bool) :
  run (4*q) (bPop q L ys) =
    ⟨L, false, oppairs q ++ ys, 1⟩ := by
  induction q generalizing ys with
  | zero => simp [bPop, oppairs, run]
  | succ q ih =>
    have ht : 4*(q+1) = 4+(4*q) := by omega
    rw [ht, run_add, bPop_step, ih]
    have hR : oppairs q ++ (false::true::ys) =
        oppairs (q+1) ++ ys := by
      calc
        _ = (oppairs q ++ [false,true]) ++ ys := by simp [List.append_assoc]
        _ = ([false,true] ++ oppairs q) ++ ys := by rw [oppairs_comm_one]
        _ = _ := by simp [oppairs]
    exact congrArg (fun z : List Bool => Cfg.mk L false z 1) hR

/-- E boundary with any number of 10 pairs before three consecutive ones. -/
def eTriplePairs (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs m ++ [true,true], false,
    pairs q ++ ([true,true,true] ++ ys), 4⟩

theorem eTriplePairs_two (m q : Nat) (ys : List Bool) :
  run 2 (eTriplePairs m q ys) =
    scanStart (q+1) (pairs m ++ [true,true]) ([true,true,true] ++ ys) := by
  simp [eTriplePairs, scanStart, run, step, goL, goR, pairs]

/-- All q: the initial 10 stack is scanned then reversed in a four-step pump. -/
theorem eTriplePairs_front (m q : Nat) (ys : List Bool) :
  run (6*q+16) (eTriplePairs m q ys) =
    sweepB m (oppairs (q+2) ++ false::ys) := by
  have ht : 6*q+16 = (2+2*(q+1)) + (8+4*(q+1)) := by omega
  rw [ht, run_add (2+2*(q+1)) (8+4*(q+1)),
    run_add 2 (2*(q+1)), eTriplePairs_two, scan_run]
  change run (8+4*(q+1))
    (⟨oppairs (q+1) ++ (pairs m ++ [true,true]), false,
      [true,true,true] ++ ys, 0⟩ : Cfg) = _
  rw [run_add 8 (4*(q+1)), aTriple8]
  change run (4*(q+1))
    (bPop (q+1) (pairs m ++ [true,true]) ([false,true,false] ++ ys)) = _
  rw [bPop_run]
  have hR : oppairs (q+1) ++ ([false,true,false] ++ ys) =
      oppairs (q+2) ++ false::ys := by
    calc
      _ = (oppairs (q+1) ++ [false,true]) ++ false::ys := by
        simp [List.append_assoc]
      _ = ([false,true] ++ oppairs (q+1)) ++ false::ys := by
        rw [oppairs_comm_one]
      _ = _ := by simp [oppairs]
  exact congrArg (fun z : List Bool => sweepB m z) hR

/-- Arbitrary q, m, and right suffix, all exact primitive steps. -/
theorem eTriplePairs_run (m q : Nat) (ys : List Bool) :
  run (2*m+6*q+19) (eTriplePairs m q ys) =
    ⟨[], false, List.replicate (2*m+3) true ++
      (oppairs (q+2) ++ false::ys), 5⟩ := by
  have ht : 2*m+6*q+19 = (6*q+16)+(2*m+3) := by omega
  rw [ht, run_add, eTriplePairs_front, sweepB_run]

/-- Universal F macro from 0(10)^q111, for ALL k,q and suffixes. -/
theorem full_E_triple_pairs (k q : Nat) (ys : List Bool) :
  run (12*k*k+49*k+58+6*q)
    (init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ ([true,true,true] ++ ys)))) =
    ⟨[], false, List.replicate (8*k+9) true ++
      (oppairs (q+2) ++ false::ys), 5⟩ := by
  have ht : 12*k*k+49*k+58+6*q =
    (12*k*k+41*k+33)+(2*(4*k+3)+6*q+19) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+3)+6*q+19) (eTriplePairs (4*k+3) q ys) = _
  rw [eTriplePairs_run]
  rw [show 2*(4*k+3)+3 = 8*k+9 by omega]

#print axioms aTriple8
#print axioms bPop_run
#print axioms eTriplePairs_front
#print axioms eTriplePairs_run
#print axioms full_E_triple_pairs
end CryptidBoundary
