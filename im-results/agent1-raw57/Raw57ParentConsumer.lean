import Raw57ParentBridge
import Raw57RAData
import Raw57RB0Data
import Raw57RC0Data
import Raw57RB1Data
import Raw57RC1Data
import Raw57RE1Data
import Raw57RE0Data
import Raw57RF0Data
import Raw57LB0Data
import Raw57LC0Data
import Raw57LD0Data
import Raw57RA1Data
import Raw57RF1Data
import Raw57LC1Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw57Consumer
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent1Raw57Parent

theorem early_bounds : ∀ mv ∈ early, ∀ m, compatible (child mv) m → WeightedBound 273 m := by
  intro mv hmv m hm
  simp only [early, List.mem_cons, List.not_mem_nil, or_false] at hmv
  rcases hmv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BB6.Agent6Raw57RA.all_completions m hm
  · exact lift (by decide : 152 ≤ 273) (BB6.Agent6Raw57RB0.all_completions m hm)
  · exact lift (by decide : 141 ≤ 273) (BB6.Agent6Raw57RC0.all_completions m hm)
  · exact lift (by decide : 180 ≤ 273) (BB6.Agent6Raw57RB1.all_completions m hm)
  · exact lift (by decide : 156 ≤ 273) (BB6.Agent6Raw57RC1.all_completions m hm)
  · exact lift (by decide : 152 ≤ 273) (BB6.Agent6Raw57RE1.all_completions m hm)
  · exact lift (by decide : 191 ≤ 273) (BB6.Agent6Raw57RE0.all_completions m hm)
  · exact lift (by decide : 245 ≤ 273) (BB6.Agent6Raw57RF0.all_completions m hm)

theorem middle_bounds : ∀ mv ∈ middle, ∀ m, compatible (child mv) m → WeightedBound 629 m := by
  intro mv hmv m hm
  simp only [middle, List.mem_cons, List.not_mem_nil, or_false] at hmv
  rcases hmv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lift (by decide : 225 ≤ 629) (BB6.Agent1Raw57LB0.all_completions m hm)
  · exact BB6.Agent1Raw57LC0.all_completions m hm
  · exact lift (by decide : 324 ≤ 629) (BB6.Agent1Raw57LD0.all_completions m hm)
  · exact lift (by decide : 382 ≤ 629) (BB6.Agent1Raw57RA1.all_completions m hm)
  · exact lift (by decide : 230 ≤ 629) (BB6.Agent1Raw57RF1.all_completions m hm)
  · exact lift (by decide : 272 ≤ 629) (BB6.Agent6Raw57LC1.all_completions m hm)

theorem parent_five (m : Machine) (hm : compatible parent m) :
    WeightedBound 629 m ∨ ∃ mv ∈ residual, compatible (child mv) m :=
  parent_dichotomy629 early_bounds middle_bounds m hm

theorem cover_at_target (B : Nat) (hB : 629 ≤ B)
    (hTail : ∀ mv ∈ residual, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) parent :=
  BB6.Agent1Raw57Parent.cover_at_target B hB early_bounds middle_bounds hTail

/-- The accepted 1LA theorem discharges one of the five parent residuals.
    This leaves exactly four independent branch Covers to be supplied. -/
theorem cover_at_target_from_four (B : Nat) (hB : 1613 ≤ B)
    (hLA : ∀ m, compatible (child ⟨true,false,0⟩) m → WeightedBound 1613 m)
    (hLB : Cover (WeightedBound B) (child ⟨true,false,1⟩))
    (hLE : Cover (WeightedBound B) (child ⟨true,false,4⟩))
    (h0LF : Cover (WeightedBound B) (child ⟨false,false,5⟩))
    (h1LF : Cover (WeightedBound B) (child ⟨true,false,5⟩)) :
    Cover (WeightedBound B) parent := by
  have hLA' : Cover (WeightedBound B) (child ⟨true,false,0⟩) := by
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (hLA m hm k d hk hd) hB
  have hTail : ∀ mv ∈ residual, Cover (WeightedBound B) (child mv) := by
    intro mv hmv
    simp only [residual, List.mem_cons, List.not_mem_nil, or_false] at hmv
    rcases hmv with rfl | rfl | rfl | rfl | rfl
    · exact hLA'
    · exact hLB
    · exact hLE
    · exact h0LF
    · exact h1LF
  exact cover_at_target B (by omega) hTail

#print axioms early_bounds
#print axioms middle_bounds
#print axioms parent_five
#print axioms cover_at_target
#print axioms cover_at_target_from_four
end BB6.Agent1Raw57Consumer
