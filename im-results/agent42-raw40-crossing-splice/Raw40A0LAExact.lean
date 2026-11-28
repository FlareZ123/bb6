import Raw40A0LABase
import Raw40C0LA0LBAll
import Raw40C0LA0LEAll
import Raw40C0LA0RBAll
import Raw40C0LA0RDAll
import Raw40C0LA0REAll
import Raw40C0LA1LAAll
import Raw40C0LAC1LBAll
import Raw40C0LA1LCAll
import Raw40C0LA1LEAll
import Raw40C0LA1RBAll
import Raw40C0LA1RCAll
import Raw40C0LA1REAll
import Raw40A0LA0REWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LAExact
open BB6Coverage BB6.Agent47CanonicalFrontier
theorem eq0LB : BB6.Agent19Raw40.A0LA.child ⟨false,false,1⟩ = BB6.Agent19Raw40.Raw40C0LA0LB.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq0LE : BB6.Agent19Raw40.A0LA.child ⟨false,false,4⟩ = BB6.Agent19Raw40.Raw40C0LA0LE.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq0RB : BB6.Agent19Raw40.A0LA.child ⟨false,true,1⟩ = BB6.Agent19Raw40.Raw40C0LA0RB.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq0RD : BB6.Agent19Raw40.A0LA.child ⟨false,true,3⟩ = BB6.Agent19Raw40.Raw40C0LA0RD.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq0RE : BB6.Agent19Raw40.A0LA.child ⟨false,true,4⟩ = BB6.Agent19Raw40.Raw40C0LA0RE.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq1LA : BB6.Agent19Raw40.A0LA.child ⟨true,false,0⟩ = BB6.Agent19Raw40.Raw40C0LA1LA.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq1LB : BB6.Agent19Raw40.A0LA.child ⟨true,false,1⟩ = BB6.Agent19Raw40.Raw40C0LAC1LB.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq1LC : BB6.Agent19Raw40.A0LA.child ⟨true,false,2⟩ = BB6.Agent19Raw40.Raw40C0LA1LC.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq1LE : BB6.Agent19Raw40.A0LA.child ⟨true,false,4⟩ = BB6.Agent19Raw40.Raw40C0LA1LE.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq1RB : BB6.Agent19Raw40.A0LA.child ⟨true,true,1⟩ = BB6.Agent19Raw40.Raw40C0LA1RB.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq1RC : BB6.Agent19Raw40.A0LA.child ⟨true,true,2⟩ = BB6.Agent19Raw40.Raw40C0LA1RC.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)
theorem eq1RE : BB6.Agent19Raw40.A0LA.child ⟨true,true,4⟩ = BB6.Agent19Raw40.Raw40C0LA1RE.p :=
  BB6.Agent19Raw40.A0LA.equalTable_sound _ _ (by decide)

/-- Every one of the twelve exact canonical residual children of A1=0LA
    has its source-proved local weighted bound. -/
theorem children :
    ∀ e ∈ BB6.Agent19Raw40.A0LA.bounds, ∀ m,
      TNFQuotientCompatible (BB6.Agent19Raw40.A0LA.child e.1) m → WeightedBound e.2 m := by
  intro e he m hm
  simp only [BB6.Agent19Raw40.A0LA.bounds, List.mem_cons, List.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · rw [eq0LB] at hm
    exact BB6.Agent19Raw40.Raw40C0LA0LB.all_quotient m hm
  · rw [eq0LE] at hm
    exact BB6.Agent19Raw40.Raw40C0LA0LE.all_quotient m hm
  · rw [eq0RB] at hm
    exact BB6.Agent19Raw40.Raw40C0LA0RB.all_quotient m hm
  · rw [eq0RD] at hm
    exact BB6.Agent19Raw40.Raw40C0LA0RD.all_quotient m hm
  · rw [eq0RE] at hm
    exact BB6.Agent19Raw40.Raw40C0LA0RE.all_quotient m hm
  · rw [eq1LA] at hm
    exact BB6.Agent19Raw40.Raw40C0LA1LA.all_quotient m hm
  · rw [eq1LB] at hm
    exact BB6.Agent19Raw40.Raw40C0LAC1LB.all_quotient m hm
  · rw [eq1LC] at hm
    exact BB6.Agent19Raw40.Raw40C0LA1LC.all_quotient m hm
  · rw [eq1LE] at hm
    exact BB6.Agent19Raw40.Raw40C0LA1LE.all_quotient m hm
  · rw [eq1RB] at hm
    exact BB6.Agent19Raw40.Raw40C0LA1RB.all_quotient m hm
  · rw [eq1RC] at hm
    exact BB6.Agent19Raw40.Raw40C0LA1RC.all_quotient m hm
  · rw [eq1RE] at hm
    exact BB6.Agent19Raw40.Raw40C0LA1RE.all_quotient m hm

/-- Unconditional weighted upper bound for the complete six-hole A1=0LA
    Raw40 subfamily. -/
theorem upper :
    ∀ m, TNFQuotientCompatible BB6.Agent19Raw40.A0LA.p m → WeightedBound 22169 m :=
  BB6.Agent19Raw40.A0LA.close children

/-- Exact weighted maximum of the complete six-hole A1=0LA subfamily.
    The upper half is the twelve-child composition; the lower half is the
    explicit 22,168-step, zero-delay witness. -/
theorem exact_weighted :
    (∀ m, compatible BB6.Agent19Raw40.A0LA.p m → WeightedBound 22169 m) ∧
    ∀ B < 22169, ∃ m, compatible BB6.Agent19Raw40.A0LA.p m ∧ ¬ WeightedBound B m := by
  refine ⟨?_, BB6.Agent42Raw40A0LA0REWitness.lower_sharp⟩
  intro m hm
  exact upper m (compatible_quotient hm)

#print axioms children
#print axioms upper
#print axioms exact_weighted
end BB6.Agent42Raw40A0LAExact
