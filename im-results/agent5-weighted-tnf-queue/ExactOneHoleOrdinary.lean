import WeightedTNF
import FastPhaseTree
set_option maxHeartbeats 0

/-
A first undefined transition of an otherwise ordinary 6-state machine gives
an *exact ordinary-score* upper bound n+1, unlike the padded WeightedBound
n+6 used for blank-delay/normalization certification.
The theorem holds without first-one normalization and with no delay padding.
-/
namespace BB6.Agent5ExactOneHole
open BB6Coverage BB6.Agent13BlankDelay

/-- Explicit ordinary halting time ≤ B, or nonhalting forever. -/
def OrdinaryBound (B : Nat) (m : Machine) : Prop :=
  (∃ n : Nat, HaltsAfter m n ∧ n + 1 ≤ B) ∨ NeverHalts m

/-- If a partial machine has one undefined slot, the first-hole plain score
    is at most n+1 for every compatible complete machine. -/
theorem last_hole_exact
    (B : Nat) (p : PartialMachine) (n : Nat) (c : Config)
    (hr : knownRun p n = some c)
    (hu : p (readSlot c) = none)
    (hrest : ∀ slot, slot ≠ readSlot c →
      ∃ mv, p slot = some (some mv))
    (hb : n + 1 ≤ B) :
    ∀ m, compatible p m → OrdinaryBound B m := by
  intro m hc
  cases ht : m (readSlot c) with
  | none =>
      left
      refine ⟨n, first_hole_halts p n c hr hu m ?_, hb⟩
      intro slot t hs
      by_cases he : slot = readSlot c
      · subst slot
        simp [refine] at hs
        subst t
        exact ht
      · exact hc slot t (by simpa [refine, he] using hs)
  | some mv =>
      right
      apply all_ordinary_never m
      intro slot
      by_cases he : slot = readSlot c
      · subst slot
        exact ⟨mv, ht⟩
      · obtain ⟨v, hv⟩ := hrest slot he
        exact ⟨v, hc slot _ hv⟩

#print axioms last_hole_exact
end BB6.Agent5ExactOneHole
