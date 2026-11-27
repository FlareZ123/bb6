import Raw40A1LABase
import Raw40C1LA0LCAll
import Raw40C1LA0LEAll
import Raw40C1LA0RCAll
import Raw40C1LA0REAll
import Raw40C1LA1LBAll
import Raw40C1LA1LCAll
import Raw40C1LA1LEAll
import Raw40C1LA1RCAll
import Raw40C1LA1REAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1LA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

theorem children : ∀ e ∈ bounds, ∀ m, TNFQuotientCompatible (child e.1) m → WeightedBound e.2 m := by
  intro e he
  simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · intro m hm
    have eq : child ⟨false,false,2⟩ = Raw40C1LA0LC.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA0LC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,false,4⟩ = Raw40C1LA0LE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA0LE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,2⟩ = Raw40C1LA0RC.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA0RC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨false,true,4⟩ = Raw40C1LA0RE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA0RE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,1⟩ = Raw40C1LA1LB.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA1LB.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,2⟩ = Raw40C1LA1LC.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA1LC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,false,4⟩ = Raw40C1LA1LE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA1LE.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,true,2⟩ = Raw40C1LA1RC.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA1RC.all_quotient m (eq ▸ hm)
  · intro m hm
    have eq : child ⟨true,true,4⟩ = Raw40C1LA1RE.p := equalTable_sound _ _ (by decide)
    exact Raw40C1LA1RE.all_quotient m (eq ▸ hm)

theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound 790 m := close children

theorem all : ∀ m, compatible p m → WeightedBound 790 m := by
  intro m hm
  exact all_quotient m (compatible_quotient hm)

-- 1RB1LA_1RC1RE_0RD1RC_1LD1LA_HHH0LF_1RC1LF
def witness : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨true,false,0⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,true,4⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨true,true,2⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,false,0⟩
  | 4,true => some ⟨false,false,5⟩
  | 5,false => some ⟨true,true,2⟩
  | 5,true => some ⟨true,false,5⟩
  | _,_ => none

theorem witness_compatible : compatible p witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem witness_halts : HaltsAfter witness 789 := by
  constructor <;> rfl
theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

theorem exact_weighted : (∀ m, compatible p m → WeightedBound 790 m) ∧
    ∀ B < 790, ∃ m, compatible p m ∧ ¬ WeightedBound B m := by
  refine ⟨all, ?_⟩
  intro B hB
  refine ⟨witness, witness_compatible, ?_⟩
  intro hb
  have h := hb 789 0 witness_halts witness_delay
  omega

#print axioms children
#print axioms all_quotient
#print axioms exact_weighted
end BB6.Agent19Raw40.A1LA
