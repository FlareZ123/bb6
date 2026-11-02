import Lean.Elab.Tactic.Omega
import CryptidSix

set_option maxHeartbeats 8000000
namespace CryptidBoundary

/-- C-on-one reverse sweep consuming an arbitrarily long 01 stack. -/
def cWalk (n : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs n ++ L, true, ys, 2⟩

theorem cWalk_step (n : Nat) (L ys : List Bool) :
  run 2 (cWalk (n+1) L ys) = cWalk n L (true::true::ys) := by
  simp [cWalk, oppairs, run, step, goL, goR]

theorem cWalk_run (n : Nat) (L ys : List Bool) :
  run (2*n) (cWalk n L ys) =
    ⟨L, true, List.replicate (2*n) true ++ ys, 2⟩ := by
  induction n generalizing ys with
  | zero => simp [cWalk, oppairs, run]
  | succ n ih =>
    have ht : 2*(n+1) = 2+(2*n) := by omega
    rw [ht, run_add, cWalk_step, ih]
    have hR : List.replicate (2*n) true ++ (true::true::ys) =
        List.replicate (2+2*n) true ++ ys := by
      calc
        _ = (List.replicate (2*n) true ++ List.replicate 2 true) ++ ys := by
          simp [List.append_assoc]
        _ = List.replicate (2*n+2) true ++ ys := by
          rw [List.replicate_append_replicate]
        _ = _ := by rw [show 2*n+2 = 2+2*n by omega]
    exact congrArg (fun z : List Bool => Cfg.mk L true z 2) hR

/-- Initial A-on-zero state after the forward 10-pair scan. -/
def aCloseStart (n m : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs n ++ (pairs (m+2) ++ [true,true]), false, false::ys, 0⟩

theorem aClose_two (n m : Nat) (ys : List Bool) :
  run 2 (aCloseStart n m ys) =
    cWalk n (pairs (m+2) ++ [true,true]) (true::ys) := by
  simp [aCloseStart, cWalk, run, step, goL, goR]

theorem cBase (m : Nat) (ys : List Bool) :
  run 4 (⟨pairs (m+2) ++ [true,true], true, ys, 2⟩ : Cfg) =
    sweepB m ([false,true,true,true] ++ ys) := by
  simp [sweepB, run, step, goL, goR, pairs]

/-- Uniform close of all scanned right pairs, preserving the arbitrary tail. -/
theorem aClose_run (n m : Nat) (ys : List Bool) :
  run (2*n+6) (aCloseStart n m ys) =
    sweepB m (false :: List.replicate (2*n+4) true ++ ys) := by
  have ht : 2*n+6 = (2+2*n)+4 := by omega
  rw [ht, run_add (2+2*n) 4, run_add 2 (2*n),
    aClose_two, cWalk_run, cBase]
  have hp :
      [false,true,true,true] ++
        (List.replicate (2*n) true ++ true::ys) =
      false :: List.replicate (2*n+4) true ++ ys := by
    calc
      _ = false ::
          ((List.replicate 3 true ++ List.replicate (2*n) true) ++
            List.replicate 1 true ++ ys) := by
          simp [List.append_assoc]
      _ = false :: (List.replicate (3+2*n+1) true ++ ys) := by
          rw [List.replicate_append_replicate,
            List.replicate_append_replicate]
      _ = _ := by
          rw [show 3+2*n+1 = 2*n+4 by omega]
          simp only [List.cons_append]
  exact congrArg (fun z : List Bool => sweepB m z) hp

/-- Any number of 10 pairs followed by 0 at an E boundary. -/
def ePairs (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true], false,
    pairs q ++ (false::ys), 4⟩

theorem ePairs_two (m q : Nat) (ys : List Bool) :
  run 2 (ePairs m q ys) =
    scanStart (q+1) (pairs (m+2) ++ [true,true]) (false::ys) := by
  simp [ePairs, scanStart, run, step, goL, goR, pairs]

/-- All-parameter uniform E-to-B rule, independent of the suffix. -/
theorem ePairs_toB (m q : Nat) (ys : List Bool) :
  run (4*q+12) (ePairs m q ys) =
    sweepB m (false :: List.replicate (2*q+6) true ++ ys) := by
  have ht : 4*q+12 = (2+2*(q+1))+(2*(q+1)+6) := by omega
  rw [ht, run_add (2+2*(q+1)) (2*(q+1)+6),
    run_add 2 (2*(q+1)), ePairs_two, scan_run]
  change run (2*(q+1)+6) (aCloseStart (q+1) m ys) = _
  rw [aClose_run]
  rw [show 2*(q+1)+4 = 2*q+6 by omega]

/-- Full raw six-state E return for all m, q and binary suffixes. -/
theorem ePairs_run (m q : Nat) (ys : List Bool) :
  run (2*m+4*q+15) (ePairs m q ys) =
    ⟨[], false, List.replicate (2*m+3) true ++
      (false :: List.replicate (2*q+6) true ++ ys), 5⟩ := by
  have ht : 2*m+4*q+15 = (4*q+12)+(2*m+3) := by omega
  rw [ht, run_add, ePairs_toB, sweepB_run]

/-- Entire third-congruence F return on 0(10)^q0, for ALL k,q,ys.
    The q=0 case specializes to the earlier full_E_00 theorem. -/
theorem full_E_pairs (k q : Nat) (ys : List Bool) :
  run (12*k*k+49*k+50+4*q)
    (init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ (false::ys)))) =
    ⟨[], false, List.replicate (8*k+5) true ++
      (false :: List.replicate (2*q+6) true ++ ys), 5⟩ := by
  have ht : 12*k*k+49*k+50+4*q =
    (12*k*k+41*k+33)+(2*(4*k+1)+4*q+15) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+1)+4*q+15) (ePairs (4*k+1) q ys) = _
  rw [ePairs_run]
  rw [show 2*(4*k+1)+3 = 8*k+5 by omega]

#print axioms cWalk_run
#print axioms aClose_run
#print axioms ePairs_toB
#print axioms ePairs_run
#print axioms full_E_pairs
end CryptidBoundary
