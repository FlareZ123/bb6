import Raw124New0LBCut
import ResidualCover
import Raw124M264
import Raw124M267
import Raw124M448

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124ZeroLBComplete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover
open BB6.Agent2Raw124New0LB

theorem lift (B C : Nat) (h : B ≤ C) (m : Machine) (hb : WeightedBound B m) :
    WeightedBound C m := by
  intro n d hhalt hdelay
  exact Nat.le_trans (hb n d hhalt hdelay) h

def seals : List (Accepted 4136175) :=
  [⟨BB6.Agent2.Raw124M264.table, fun m hm =>
      lift 520988 4136175 (by decide) m (BB6.Agent2.Raw124M264.bound m hm)⟩,
   ⟨BB6.Agent4.Raw124M267.table, fun m hm =>
      lift 79911 4136175 (by decide) m (BB6.Agent4.Raw124M267.bound m hm)⟩,
   ⟨BB6.Agent4.Raw124M448.table, BB6.Agent4.Raw124M448.bound⟩]

theorem no_open : (remaining seals residuals).length = 0 := by decide

theorem bound_all : ∀ m, compatible branch m → WeightedBound 4136175 m := by
  intro m hm
  have hcut : ∀ m, compatible branch m → WeightedBound 4136175 m ∨
      ∃ e ∈ residuals, compatible e.2 m := by
    intro t ht
    rcases branch_sound t ht with hb | hopen
    · exact Or.inl (lift 3006 4136175 (by decide) t hb)
    · exact Or.inr hopen
  rcases consume seals hcut m hm with hb | ⟨e,he,_⟩
  · exact hb
  · have hnil : remaining seals residuals = [] := List.length_eq_zero_iff.mp no_open
    rw [hnil] at he
    simp at he

#print axioms no_open
#print axioms bound_all
end BB6.Agent2Raw124ZeroLBComplete
