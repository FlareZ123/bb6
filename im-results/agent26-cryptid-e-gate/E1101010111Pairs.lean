import Lean.Elab.Tactic.Omega
import CryptidPairs

namespace BB6.Agent26E1101010111

open CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def wordE (ys : List Bool) : List Bool :=
  [true,true,false,true,false,true,false,true,true,true] ++ ys

def wordD (ys : List Bool) : List Bool :=
  [true,true,false,true,false,true,false,true,false,true,false] ++ ys

def eStart (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true], false,
    pairs q ++ wordE ys, 4⟩

/-- Original E input scans any rightward (10)^q prefix. -/
theorem e_two (m q : Nat) (ys : List Bool) :
    run 2 (eStart m q ys) =
      scanStart (q+1) (pairs (m+2) ++ [true,true]) (wordE ys) := by
  simp [eStart, scanStart, wordE, run, step, goL, goR, pairs]

theorem e_scan (m q : Nat) (ys : List Bool) :
    run (2*q+4) (eStart m q ys) =
      ⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]),
        false, wordE ys, 0⟩ := by
  have ht : 2*q+4 = 2+2*(q+1) := by omega
  rw [ht, run_add, e_two, scan_run]
  rfl

/-- A 33-step terminal word transform, uniform in the complete left stack. -/
theorem a_turn (L ys : List Bool) :
    run 33 (⟨false::L, false, wordE ys, 0⟩ : Cfg) =
      ⟨L, false, wordD ys, 3⟩ := by
  simp [wordE, wordD, run, step, goL, goR]

theorem e_mid (m q : Nat) (ys : List Bool) :
    run (2*q+37) (eStart m q ys) =
      ⟨true :: (oppairs q ++ (pairs (m+2) ++ [true,true])),
        false, wordD ys, 3⟩ := by
  have ht : 2*q+37 = (2*q+4)+33 := by omega
  rw [ht, run_add, e_scan]
  change run 33
    (⟨false::true::(oppairs q ++ (pairs (m+2) ++ [true,true])),
      false, wordE ys, 0⟩ : Cfg) = _
  exact a_turn _ ys

/-- D/0 begins the source-certified C/1 reverse (01)^q sweep. -/
theorem d_to_c (m q : Nat) (ys : List Bool) :
    run 1 (⟨true :: (oppairs q ++ (pairs (m+2) ++ [true,true])),
         false, wordD ys, 3⟩ : Cfg) =
      cWalk q (pairs (m+2) ++ [true,true]) (true :: wordD ys) := by
  simp [cWalk, run, step, goL, goR]

def bWord (q : Nat) (ys : List Bool) : List Bool :=
  [false,true,true,true] ++
    (List.replicate (2*q) true ++ (true::wordD ys))

/-- The fixed C finish follows cWalk_run and cBase without rederiving them. -/
theorem e_to_b (m q : Nat) (ys : List Bool) :
    run (4*q+42) (eStart m q ys) =
      sweepB m (bWord q ys) := by
  have ht : 4*q+42 = (2*q+37)+(1+(2*q)+4) := by omega
  rw [ht, run_add, e_mid]
  rw [show 1+2*q+4=1+(2*q+4) by omega, run_add, d_to_c]
  rw [show 2*q+4=(2*q)+4 by omega, run_add, cWalk_run]
  change run 4
    (⟨pairs (m+2) ++ [true,true], true,
       List.replicate (2*q) true ++ (true::wordD ys), 2⟩ : Cfg) = _
  rw [cBase]
  rfl

/-- All m,q,suffixes; the symbolic B sweep ends in actual F/0. -/
theorem e_run (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+45) (eStart m q ys) =
      ⟨[], false, List.replicate (2*m+3) true ++ bWord q ys, 5⟩ := by
  have ht : 2*m+4*q+45 = (4*q+42)+(2*m+3) := by omega
  rw [ht, run_add, e_to_b, sweepB_run]

/-- Original-machine, arbitrary-suffix full F/0 return at E suffix
    (10)^q 1101010111. No blank-tape reachability is asserted. -/
theorem full_E_1101010111_pairs (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+80+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[], false, List.replicate (8*k+5) true ++ bWord q ys, 5⟩ := by
  have ht : 12*k*k+49*k+80+4*q =
    (12*k*k+41*k+33)+(2*(4*k+1)+4*q+45) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+1)+4*q+45) (eStart (4*k+1) q ys) = _
  rw [e_run]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms a_turn
#print axioms e_run
#print axioms full_E_1101010111_pairs

end BB6.Agent26E1101010111
