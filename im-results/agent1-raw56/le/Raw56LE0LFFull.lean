import Raw56LE0LFPartialAll
import Raw56LE0LFMotif3613

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56.LE0LFFull
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent1Raw56.LE0LFPartial
open BB6.Agent1Raw56.LE0LFMotif3613

theorem residual_head_eq : remaining1.head!.2 = M3613.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem remaining_singleton : remaining1 = [remaining1.head!] := by
  cases h : remaining1 with
  | nil =>
    have hc := count1
    rw [h] at hc
    simp at hc
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b ys =>
      have hc := count1
      rw [h] at hc
      simp at hc

theorem leaf_quotient_bound (m : Machine)
    (hq : TNFQuotientCompatible M3613.table m) :
    WeightedBound 40000 m := by
  apply quotientSafe (p:=M3613.table) (B:=40000) (by decide) ?_ m hq
  intro m' hm'
  exact weighted_never 40000 m' (M3613.never m' hm')

theorem all_quotient (m : Machine)
    (hq : TNFQuotientCompatible p m) : WeightedBound 40000 m := by
  rcases sound1 m hq with hb | ⟨e, he, heq⟩
  · exact hb
  · rw [remaining_singleton] at he
    simp at he
    subst e
    rw [residual_head_eq] at heq
    exact leaf_quotient_bound m heq

theorem cover : Cover (WeightedBound 40000) p := by
  refine .leaf p ?_
  intro m hm
  exact all_quotient m (compatible_quotient hm)

#print axioms residual_head_eq
#print axioms all_quotient
#print axioms cover
end BB6.Agent1Raw56.LE0LFFull
