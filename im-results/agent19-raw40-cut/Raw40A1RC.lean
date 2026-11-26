import Raw40A1RCBase
import Raw40C1RC0LAAll
import Raw40C1RC0LBAll
import Raw40C1RC0LDAll
import Raw40C1RC0LEAll
import Raw40C1RC0RBAll
import Raw40C1RC0RCAll
import Raw40C1RC0RDAll
import Raw40C1RC0REAll
import Raw40C1RC1LBAll
import Raw40C1RC1LCAll
import Raw40C1RC1LDAll
import Raw40C1RC1LEAll
import Raw40C1RC1RBAll
import Raw40C1RC1REAll
import Raw40Round29Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

theorem children : ∀ e ∈ bounds, ∀ m, TNFQuotientCompatible (child e.1) m → WeightedBound e.2 m := by
  intro e he
  simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · intro m hm
    have eq : child ⟨false,false,0⟩ = Raw40C1RC0LA.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0LA.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,false,1⟩ = Raw40C1RC0LB.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0LB.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,false,3⟩ = Raw40C1RC0LD.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0LD.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,false,4⟩ = Raw40C1RC0LE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0LE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,1⟩ = Raw40C1RC0RB.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0RB.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,2⟩ = Raw40C1RC0RC.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0RC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,3⟩ = Raw40C1RC0RD.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0RD.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,4⟩ = Raw40C1RC0RE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC0RE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,1⟩ = Raw40C1RC1LB.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC1LB.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,2⟩ = Raw40C1RC1LC.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC1LC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,3⟩ = Raw40C1RC1LD.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC1LD.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,4⟩ = Raw40C1RC1LE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC1LE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,true,1⟩ = Raw40C1RC1RB.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC1RB.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,true,4⟩ = Raw40C1RC1RE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1RC1RE.all_quotient m (eq ▸ hm)

theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound 5729 m := close children

theorem all : ∀ m, compatible p m → WeightedBound 5729 m := by
  intro m hm
  exact all_quotient m (compatible_quotient hm)

theorem witness_compatible : compatible p Raw40C1RC1RE.witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem exact_weighted : (∀ m, compatible p m → WeightedBound 5729 m) ∧
    ∀ B < 5729, ∃ m, compatible p m ∧ ¬ WeightedBound B m := by
  refine ⟨all, ?_⟩
  intro B hB
  refine ⟨Raw40C1RC1RE.witness, witness_compatible, ?_⟩
  intro hb
  have h := hb 5728 0 Raw40C1RC1RE.witness_halts Raw40C1RC1RE.witness_delay
  omega

#print axioms children
#print axioms all_quotient
#print axioms exact_weighted
end BB6.Agent19Raw40.A1RC
