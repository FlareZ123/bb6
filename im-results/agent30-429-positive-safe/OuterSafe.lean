import PositiveZeroGate
import PhysicalSafe
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429OuterSafe

open BB6Coverage BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4CZeroSafe BB429PositiveSafe BB429ZeroRegularSafe
open BB429PositiveZeroGate BB429PhysicalGuardSafe
open BB429PhysicalFrontier BB429PhysicalBridge

/-- Exact cost of one complete outer Junc chart return: all positive-u
    reductions followed by the single regular zero-u return. -/
def outerCost (U v : Nat) : Nat :=
  juncPosFullTime U v + (2*(v+2*U)+27)

/-- Entire high-budget outer Junc branch is C/0-free at every primitive
    step, for all initial counters satisfying w >= 2U+3.
    This combines the complete positive and regular zero-u return proofs. -/
theorem junc_outer_safe (U v w : Nat) (hw : 2*U+3 ≤ w) :
    runSafe (outerCost U v) (junc U v w) =
      some (junc (v+2*U+3) 0 ((w-2*U)-3)) := by
  have hf := junc_positive_iter_safe U U v w (by omega) (by omega)
  have hs := junc0_regular_safe (v+2*U) (w-2*U) (by omega)
  unfold outerCost
  rw [runSafe_add,hf]
  simp only [Option.bind_some]
  simpa only [Nat.sub_self] using hs

/-- The complete outer branch is C/0-free on the actual physical
    six-state tape at every primitive prefix of the exact source cost. -/
theorem physical_outer_no_czero (U v w t : Nat)
    (c : Config) (hrep : Represents (junc U v w) c)
    (hw : 2*U+3 ≤ w) (ht : t < outerCost U v) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      ¬(d.state.val = 2 ∧ d.tape d.head = false) := by
  exact physical_guarded_prefix (outerCost U v) t
    (junc U v w) (junc (v+2*U+3) 0 ((w-2*U)-3))
    c hrep (junc_outer_safe U v w hw) ht

/-- Original raw-machine physics for the exceptional positive-u, w=0
    first C/0 event: all right cells are blank at that exact point. -/
theorem physical_positive_zero_first_czero (u v : Nat)
    (c : Config) (hrep : Represents (junc (u+1) v 0) c) :
    ∃ d, BB6Coverage.run target429 (2*v+10) c = some d ∧
      d.state.val = 2 ∧ d.tape d.head = false ∧
      d.tape (d.head+1) = false := by
  let zfinal : Zipper :=
    z 2 (ones (2*v+9) ++ (pairs01 u ++ ones 5)) false []
  have hz : BB429OddExcursion.run (2*v+10) (junc (u+1) v 0) =
      some zfinal :=
    runSafe_to_run (2*v+10) (junc (u+1) v 0)
      zfinal (junc_positive_w0_first_czero u v)
  obtain ⟨d,hraw,hrepd⟩ :=
    source_run_rep (2*v+10) (junc (u+1) v 0) c hrep zfinal hz
  refine ⟨d,hraw,hrepd.1,hrepd.2.1,?_⟩
  have hr := hrepd.2.2.2 0
  change d.tape (d.head+1) = false at hr
  exact hr

/-- Every earlier physical prefix of the positive-u zero-budget
    Junc avoids C/0, even with arbitrary physical head origin. -/
theorem physical_positive_zero_no_earlier_czero
    (u v t : Nat) (c : Config)
    (hrep : Represents (junc (u+1) v 0) c)
    (ht : t < 2*v+10) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      ¬(d.state.val = 2 ∧ d.tape d.head = false) := by
  exact physical_guarded_prefix (2*v+10) t
    (junc (u+1) v 0)
    (z 2 (ones (2*v+9) ++ (pairs01 u ++ ones 5)) false [])
    c hrep (junc_positive_w0_first_czero u v) ht

#print axioms junc_outer_safe
#print axioms physical_outer_no_czero
#print axioms physical_positive_zero_first_czero
#print axioms physical_positive_zero_no_earlier_czero

end BB429OuterSafe
