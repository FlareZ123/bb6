import Raw40C0LA1LBAll
import Raw40C0LA0LBAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.ClosedFilter
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

def equalTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => [false,true].all fun b => decide (p (s,b)=q (s,b))
theorem equalTable_sound (p q : PartialMachine) (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨q',b⟩
  have hq := List.all_eq_true.mp h q' (List.mem_finRange q')
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq b hb)

def closed : List PartialMachine := [Raw40C0LA1LB.p, Raw40C0LA0LB.p]
theorem closed_sound {B : Nat} (hB : 1891 ≤ B) : ∀ p ∈ closed, ∀ m, TNFQuotientCompatible p m → WeightedBound B m := by
  intro p hp
  simp only [closed,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0LA1LB.all_quotient m hm k d hk hd) (by omega)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0LA0LB.all_quotient m hm k d hk hd) hB

def remaining (roster : List (List Move × PartialMachine)) := roster.filter fun e => !(closed.any (equalTable e.2))

/-- Remove the two accepted cylinders from any quotient residual list. -/
theorem filter_sound {B : Nat} (hB : 1891 ≤ B) {root : PartialMachine}
    {roster : List (List Move × PartialMachine)}
    (hroot : ∀ m, TNFQuotientCompatible root m → WeightedBound B m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m) :
    ∀ m, TNFQuotientCompatible root m → WeightedBound B m ∨ ∃ e ∈ remaining roster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hroot m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hh : closed.any (equalTable e.2) = true
    · obtain ⟨p,hp,heq⟩ := List.any_eq_true.mp hh
      have eq := equalTable_sound e.2 p heq
      exact Or.inl (closed_sound hB p hp m (eq ▸ hq))
    · exact Or.inr ⟨e,by simp [remaining,he,hh],hq⟩

#print axioms closed_sound
#print axioms filter_sound
end BB6.Agent19Raw40.ClosedFilter
