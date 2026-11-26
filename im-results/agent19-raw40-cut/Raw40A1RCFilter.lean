import Raw40A1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1RCFilter
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

/-- A table q extendsTable the assigned slots of p. -/
def extendsTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => [false,true].all fun b =>
    match p (s,b) with
    | none => true
    | some t => decide (q (s,b) = some t)

theorem extends_sound (p q : PartialMachine) (h : extendsTable p q = true)
    (m : Machine) (hm : compatible q m) : compatible p m := by
  intro s t ht
  rcases s with ⟨q',b⟩
  have hq := List.all_eq_true.mp h q' (List.mem_finRange q')
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hc := List.all_eq_true.mp hq b hb
  rw [ht] at hc
  exact hm _ _ (of_decide_eq_true hc)

theorem quotient_extends (p q : PartialMachine) (h : extendsTable p q = true)
    (m : Machine) (hm : TNFQuotientCompatible q m) : TNFQuotientCompatible p m := by
  obtain ⟨e,he,hq⟩ := hm
  exact ⟨e,he,extends_sound p q h _ hq⟩

def remaining (roster : List (List Move × PartialMachine)) := roster.filter fun e => !(extendsTable A1RC.p e.2)

/-- Directly consume the six-hole branch in any prior quotient-compatible frontier.
This also removes strict descendants, so no particular refinement depth is assumed. -/
theorem filter_sound {B : Nat} (hB : 5729 ≤ B)
    (hRC : ∀ m, TNFQuotientCompatible A1RC.p m → WeightedBound 5729 m)
    {root : PartialMachine} {roster : List (List Move × PartialMachine)}
    (hroot : ∀ m, TNFQuotientCompatible root m → WeightedBound B m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m) :
    ∀ m, TNFQuotientCompatible root m → WeightedBound B m ∨ ∃ e ∈ remaining roster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hroot m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hh : extendsTable A1RC.p e.2 = true
    · left
      have hb := hRC m (quotient_extends _ _ hh m hq)
      intro k d hk hd; exact Nat.le_trans (hb k d hk hd) hB
    · exact Or.inr ⟨e,by simp [remaining,he,hh],hq⟩

#print axioms extends_sound
#print axioms filter_sound
end BB6.Agent19Raw40.A1RCFilter
