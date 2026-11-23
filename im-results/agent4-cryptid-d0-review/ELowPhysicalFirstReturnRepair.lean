import Lean.Elab.Tactic.Omega
import PrefixNoF
import CryptidPairs
import E111FirstReturn
import NoEarlierF

/-!
# Corrected E(10)^q0 physical first-return argument

The draft PairsFirstReturn.cBase_noF is too strong: C/1 -> D/1 -> F
occurs during the four-step C-to-B closing bridge.  That F visit has
nonblank physical left tape, and is not a complete F/0 section return.

This file deliberately uses NoReturn / IsPhysicalReturn instead of
NoF for that bridge.  It is a source-level repair draft; it has NOT
yet passed a Lean compiler/axiom audit in this invocation.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.CryptidELowPhysicalRepair

open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidFirstReturn

private theorem noF_to_noReturn (c : Cfg) (n : Nat)
    (hf : NoF c n) : NoReturn c n := by
  intro t ht hphys
  exact hf t ht hphys.1

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hs : t < a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq, run_add, he]
    exact hd (t-a) (by omega)

private theorem appendNoReturn (c d : Cfg) (a b : Nat)
    (hc : NoReturn c a) (he : run a c = d) (hd : NoReturn d b) :
    NoReturn c (a+b) := by
  intro t ht
  by_cases hs : t < a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq, run_add, he]
    exact hd (t-a) (by omega)

theorem scanner_noF (n : Nat) (L ys : List Bool) :
    NoF (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      intro t ht
      by_cases hs : t < 2
      · have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [scanStart, run, step, goL, goR, pairs]
      · have htime : t=2+(t-2) := by omega
        rw [htime,run_add,scan_step]
        exact ih ([false,true]++L) ys (t-2) (by omega)

theorem ePairs_start_noF (m q : Nat) (ys : List Bool) :
    NoF (ePairs m q ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [ePairs,run,step,goL,goR,pairs]

theorem aCloseStart_noF (n m : Nat) (ys : List Bool) :
    NoF (aCloseStart n m ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [aCloseStart,run,step,goL,goR,pairs,oppairs]

private theorem cWalk_two_noF (n : Nat) (L ys : List Bool) :
    NoF (cWalk (n+1) L ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [cWalk,run,step,goL,goR,oppairs]

theorem cWalk_noF (n : Nat) (L ys : List Bool) :
    NoF (cWalk n L ys) (2*n) := by
  induction n generalizing ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have htime : 2*(n+1)=2+2*n := by omega
      rw [htime]
      exact appendNoF
        (cWalk (n+1) L ys) (cWalk n L (true::true::ys))
        2 (2*n) (cWalk_two_noF n L ys)
        (cWalk_step n L ys) (ih (true::true::ys))

/-- Diagnostic: the old stronger no-F lemma is false at time two. -/
theorem cBase_internal_F (m : Nat) (ys : List Bool) :
    (run 2 (⟨pairs (m+2) ++ [true,true], true, ys, 2⟩ : Cfg)).st = 5 := by
  simp [run,step,goL,goR,pairs]

/-- The intermediate F visit in the C-to-B close has a nonempty
    physical left stack.  All four source steps lack a *physical*
    F/0 return even though state F is visited at step two. -/
private theorem cBase_noReturn (m : Nat) (ys : List Bool) :
    NoReturn (⟨pairs (m+2) ++ [true,true], true, ys, 2⟩ : Cfg) 4 := by
  intro t ht hphys
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,run,step,goL,goR,pairs] at hphys

/-- No physically complete F/0 section arises during E(10)^q0's
    transition from E to the final leftward B sweep. -/
theorem ePairs_toB_noReturn (m q : Nat) (ys : List Bool) :
    NoReturn (ePairs m q ys) (4*q+12) := by
  let L : List Bool := pairs (m+2) ++ [true,true]
  have hb : NoReturn
      (⟨L, true, List.replicate (2*(q+1)) true ++ (true::ys), 2⟩ : Cfg) 4 := by
    dsimp [L]
    exact cBase_noReturn m _
  have hc : NoReturn (cWalk (q+1) L (true::ys))
      (2*(q+1)+4) :=
    appendNoReturn
      (cWalk (q+1) L (true::ys))
      (⟨L, true, List.replicate (2*(q+1)) true ++ (true::ys), 2⟩ : Cfg)
      (2*(q+1)) 4
      (noF_to_noReturn _ _ (cWalk_noF (q+1) L (true::ys)))
      (cWalk_run (q+1) L (true::ys))
      hb
  have ha : NoReturn (aCloseStart (q+1) m ys)
      (2+(2*(q+1)+4)) :=
    appendNoReturn
      (aCloseStart (q+1) m ys)
      (cWalk (q+1) L (true::ys))
      2 (2*(q+1)+4)
      (noF_to_noReturn _ _ (aCloseStart_noF (q+1) m ys))
      (aClose_two (q+1) m ys)
      hc
  have hs : NoReturn
      (scanStart (q+1) L (false::ys))
      (2*(q+1)+(2+(2*(q+1)+4))) := by
    have hscan : NoF (scanStart (q+1) L (false::ys))
        (2*(q+1)) := scanner_noF (q+1) L (false::ys)
    have he : run (2*(q+1)) (scanStart (q+1) L (false::ys)) =
        aCloseStart (q+1) m ys := by
      rw [scan_run]
      rfl
    exact appendNoReturn _ _ (2*(q+1)) (2+(2*(q+1)+4))
      (noF_to_noReturn _ _ hscan) he ha
  have he : NoReturn (ePairs m q ys)
      (2+(2*(q+1)+(2+(2*(q+1)+4)))) :=
    appendNoReturn
      (ePairs m q ys)
      (scanStart (q+1) L (false::ys))
      2 (2*(q+1)+(2+(2*(q+1)+4)))
      (noF_to_noReturn _ _ (ePairs_start_noF m q ys))
      (ePairs_two m q ys)
      hs
  have htime :
      2+(2*(q+1)+(2+(2*(q+1)+4)))=4*q+12 := by omega
  simpa only [htime] using he

/-- First physical return from an E(10)^q0 boundary, for every
    parameter and arbitrary unexamined right suffix. -/
theorem ePairs_first_physical (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+15) (ePairs m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false::List.replicate (2*q+6) true ++ ys),5⟩ ∧
    NoReturn (ePairs m q ys) (2*m+4*q+15) := by
  constructor
  · exact ePairs_run m q ys
  · have htime : 2*m+4*q+15=(4*q+12)+(2*m+3) := by omega
    rw [htime]
    have htail : NoReturn
        (sweepB m (false::List.replicate (2*q+6) true ++ ys))
        (2*m+3) := by
      intro t ht hphys
      exact (sweepB_firstF m
        (false::List.replicate (2*q+6) true ++ ys) t ht) hphys.1
    exact appendNoReturn
      (ePairs m q ys)
      (sweepB m (false::List.replicate (2*q+6) true ++ ys))
      (4*q+12) (2*m+3)
      (ePairs_toB_noReturn m q ys)
      (ePairs_toB m q ys)
      htail

/-- Complete E low row, on an explicitly zero-padded physical input:
    the claimed endpoint is the first *positive physical* F/0 return.
    Canonical inputs with implicit right blanks require a padding bridge. -/
theorem full_E_pairs_first_physical (k q : Nat) :
    let n := 12*k*k+49*k+50+4*q
    let source := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ [false]))
    run n source =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true),5⟩ ∧
    ∀ t, 0<t → t<n → ¬ IsPhysicalReturn (run t source) := by
  dsimp
  constructor
  · simpa using (full_E_pairs k q [])
  · intro t hpos ht hphys
    let preCost : Nat := 12*k*k+41*k+33
    by_cases hpref : t<preCost
    · exact (prefixE_positive_noF k (pairs q ++ [false])
        t hpos hpref) hphys.1
    · have heq : t=preCost+(t-preCost) := by omega
      rw [heq,run_add,prefix_E] at hphys
      change IsPhysicalReturn (run (t-preCost) (ePairs (4*k+1) q []))
        at hphys
      exact (ePairs_first_physical (4*k+1) q []).2
        (t-preCost) (by dsimp [preCost] at *; omega) hphys

#print axioms cBase_internal_F
#print axioms ePairs_toB_noReturn
#print axioms ePairs_first_physical
#print axioms full_E_pairs_first_physical

end BB6.CryptidELowPhysicalRepair
