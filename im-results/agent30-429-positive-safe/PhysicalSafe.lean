import ZeroTwoGate
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429PhysicalGuardSafe

open BB6Coverage BB429OddExcursion BB429SourceE1Return
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4CZeroSafe BB429PositiveSafe BB429ZeroRegularSafe
open BB429ZeroTwoGate

/-- A complete guarded source certificate lifts to an all-prefix theorem
    on the genuine original six-state machine and entire physical tape. -/
theorem physical_guarded_prefix (n t : Nat) (z z' : Zipper)
    (c : Config) (hrep : Represents z c)
    (hsafe : runSafe n z = some z') (ht : t < n) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      ¬(d.state.val = 2 ∧ d.tape d.head = false) := by
  obtain ⟨p, hp, hgood⟩ :=
    runSafe_no_czero_prefix n t z z' hsafe ht
  obtain ⟨d, hraw, hrep'⟩ := source_run_rep t z c hrep p hp
  refine ⟨d,hraw,?_⟩
  intro hbad
  have hs : p.state = 2 := hrep'.1.symm.trans hbad.1
  have hc : p.current = false := hrep'.2.1.symm.trans hbad.2
  simp [hs,hc] at hgood

/-- All C/0 visits are excluded at every primitive time of a physical
    positive-u return block sequence, with arbitrary represented input. -/
theorem physical_positive_iter_no_czero (N U v w t : Nat)
    (c : Config) (hrep : Represents (junc U v w) c)
    (hU : N ≤ U) (hw : 2*N ≤ w)
    (ht : t < juncPosFullTime N v) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      ¬(d.state.val = 2 ∧ d.tape d.head = false) := by
  exact physical_guarded_prefix (juncPosFullTime N v) t
    (junc U v w) (junc (U-N) (v+2*N) (w-2*N))
    c hrep (junc_positive_iter_safe N U v w hU hw) ht

/-- The entire physical zero-u regular return, w>=3, avoids C/0 at
    every primitive prefix from any exactly represented input tape. -/
theorem physical_zero_regular_no_czero (v w t : Nat)
    (c : Config) (hrep : Represents (junc 0 v w) c)
    (hw : 3 ≤ w) (ht : t < 2*v+27) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      ¬(d.state.val = 2 ∧ d.tape d.head = false) := by
  exact physical_guarded_prefix (2*v+27) t
    (junc 0 v w) (junc (v+3) 0 (w-3))
    c hrep (junc0_regular_safe v w hw) ht

/-- The first right-two exceptional C/0 is harmless on the original
    physical tape: the entire right half-tape is blank in the exact
    reached source configuration, for every middle counter. -/
theorem physical_zero_two_first_czero (v : Nat)
    (c : Config) (hrep : Represents (junc 0 v 2) c) :
    ∃ d, BB6Coverage.run target429 (2*v+35) c = some d ∧
      d.state.val = 2 ∧ d.tape d.head = false ∧
      d.tape (d.head+1) = false := by
  let zfinal : Zipper :=
    z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5)) false []
  have hz : BB429OddExcursion.run (2*v+35) (junc 0 v 2) =
      some zfinal := runSafe_to_run (2*v+35) (junc 0 v 2)
        zfinal (junc0_w2_first_czero v)
  obtain ⟨d, hraw, hrep'⟩ :=
    source_run_rep (2*v+35) (junc 0 v 2) c hrep zfinal hz
  refine ⟨d,hraw,hrep'.1,hrep'.2.1,?_⟩
  have hr := hrep'.2.2.2 0
  change d.tape (d.head+1) = false at hr
  exact hr

/-- Arithmetic composition of the genuine raw physical run, used to
    retain the actual blank-origin time when an exact Junc entry exists. -/
private theorem physical_run_add (n t : Nat) (c : Config) :
    BB6Coverage.run target429 (n+t) c =
      (BB6Coverage.run target429 n c).bind
        (BB6Coverage.run target429 t) := by
  induction t with
  | zero => simp [BB6Coverage.run]
  | succ t ih =>
      calc
        BB6Coverage.run target429 (n+(t+1)) c =
          (BB6Coverage.run target429 (n+t) c).bind
            (rawStep target429) := by simp [BB6Coverage.run, Nat.add_succ]
        _ = ((BB6Coverage.run target429 n c).bind
              (BB6Coverage.run target429 t)).bind (rawStep target429) := by
                rw [ih]
        _ = (BB6Coverage.run target429 n c).bind
              (fun d => (BB6Coverage.run target429 t d).bind
                (rawStep target429)) := by simp [Option.bind_assoc]
        _ = (BB6Coverage.run target429 n c).bind
              (BB6Coverage.run target429 (t+1)) := by rfl

/-- Authentically blank-rooted, conditional positive-u certificate:
    every primitive instruction at an offset inside the complete
    represented return block avoids the physical halting gateway. -/
theorem blank_root_positive_iter_no_czero
    (n N U v w t : Nat) (c : Config)
    (hentry : BB6Coverage.run target429 n blank = some c)
    (hrep : Represents (junc U v w) c)
    (hU : N ≤ U) (hw : 2*N ≤ w)
    (ht : t < juncPosFullTime N v) :
    ∃ d, BB6Coverage.run target429 (n+t) blank = some d ∧
      ¬(d.state.val = 2 ∧ d.tape d.head = false) := by
  obtain ⟨d,hraw,hgood⟩ :=
    physical_positive_iter_no_czero N U v w t c hrep hU hw ht
  refine ⟨d,?_,hgood⟩
  rw [physical_run_add, hentry]
  exact hraw

/-- Authentically blank-rooted, conditional zero-u regular exclusion
    for all internal primitive times of a represented w>=3 segment. -/
theorem blank_root_zero_regular_no_czero
    (n v w t : Nat) (c : Config)
    (hentry : BB6Coverage.run target429 n blank = some c)
    (hrep : Represents (junc 0 v w) c)
    (hw : 3 ≤ w) (ht : t < 2*v+27) :
    ∃ d, BB6Coverage.run target429 (n+t) blank = some d ∧
      ¬(d.state.val = 2 ∧ d.tape d.head = false) := by
  obtain ⟨d,hraw,hgood⟩ :=
    physical_zero_regular_no_czero v w t c hrep hw ht
  refine ⟨d,?_,hgood⟩
  rw [physical_run_add, hentry]
  exact hraw

#print axioms physical_guarded_prefix
#print axioms physical_positive_iter_no_czero
#print axioms physical_zero_regular_no_czero
#print axioms physical_zero_two_first_czero
#print axioms blank_root_positive_iter_no_czero
#print axioms blank_root_zero_regular_no_czero

end BB429PhysicalGuardSafe
