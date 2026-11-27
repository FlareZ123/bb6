import Raw40A0LBBase
import Raw40C0LB0LCAll
import Raw40C0LB0LEAll
import Raw40C0LB0RCAll
import Raw40C0LB0REAll
import Raw40C0LB1LBAll
import Raw40C0LB1LCAll
import Raw40C0LB1LEAll
import Raw40C0LB1RBAll
import Raw40C0LB1RCAll
import Raw40C0LB1REAll
import Raw40A0LB561
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0LB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

theorem children : ∀ e ∈ bounds, ∀ m, TNFQuotientCompatible (child e.1) m → WeightedBound e.2 m := by
  intro e he
  simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · intro m hm
    have eq : child ⟨false,false,2⟩ = Raw40C0LB0LC.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB0LC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,false,4⟩ = Raw40C0LB0LE.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB0LE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,2⟩ = Raw40C0LB0RC.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB0RC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,4⟩ = Raw40C0LB0RE.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB0RE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,1⟩ = Raw40C0LB1LB.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB1LB.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,2⟩ = Raw40C0LB1LC.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB1LC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,4⟩ = Raw40C0LB1LE.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB1LE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,true,1⟩ = Raw40C0LB1RB.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB1RB.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,true,2⟩ = Raw40C0LB1RC.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB1RC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,true,4⟩ = Raw40C0LB1RE.p := equalTable_sound _ _ (by decide)
    exact Raw40C0LB1RE.all_quotient m (eq ▸ hm)

theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound 75493794 m := close children

theorem all : ∀ m, compatible p m → WeightedBound 75493794 m := by
  intro m hm
  exact all_quotient m (compatible_quotient hm)

theorem witness_compatible : compatible p A0LB561.witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem exact_weighted : (∀ m, compatible p m → WeightedBound 75493794 m) ∧
    ∀ B < 75493794, ∃ m, compatible p m ∧ ¬ WeightedBound B m := by
  refine ⟨all, ?_⟩
  intro B hB
  refine ⟨A0LB561.witness, witness_compatible, ?_⟩
  intro hb
  have h := hb 75493793 0 A0LB561.witness_halts A0LB561.witness_delay
  omega

#print axioms children
#print axioms all_quotient
#print axioms exact_weighted
end BB6.Agent19Raw40.A0LB
