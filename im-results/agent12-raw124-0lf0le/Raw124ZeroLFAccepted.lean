import Raw124ZeroLFParent
import Raw124ZeroLF0LE
import Raw124ZeroLF0RB
import Raw124ZeroLF0RE
import Raw124ZeroLF1LC
import Raw124ZeroLF1RA
import Raw124ZeroLF1RE
import Agent7Raw124ZeroLF0RA
import Raw124ZeroLF1LA
import Raw124ZeroLF1LB
import Raw124ZeroLF1LE
import Agent7Raw124ZeroLF1RB
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent12Raw124ZeroLFAccepted
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent12Raw124ZeroLFParent
theorem cover0LE : Cover (WeightedBound 2931) (child ⟨false,false,4⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF0LE.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF0LE.bound_all
theorem cover0RB : Cover (WeightedBound 2931) (child ⟨false,true,1⟩) :=
  transport (q := BB6.Agent4Raw124ZeroLF0RB.pChild) (by decide) (by decide)
    BB6.Agent4Raw124ZeroLF0RB.bound_all
theorem cover0RE : Cover (WeightedBound 2931) (child ⟨false,true,4⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF0RE.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF0RE.bound_all
theorem cover1LC : Cover (WeightedBound 2931) (child ⟨true,false,2⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF1LC.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF1LC.bound_all
theorem cover1RA : Cover (WeightedBound 2931) (child ⟨true,true,0⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF1RA.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF1RA.bound_all
theorem cover1RE : Cover (WeightedBound 2931) (child ⟨true,true,4⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF1RE.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF1RE.bound_all

theorem cover0RA : Cover (WeightedBound 2931) (child ⟨false,true,0⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF0RA.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF0RA.bound_all
theorem cover1LA : Cover (WeightedBound 2931) (child ⟨true,false,0⟩) :=
  transport (q := BB6.Agent32Raw124ZeroLF1LA.pChild) (by decide) (by decide)
    BB6.Agent32Raw124ZeroLF1LA.bound_all
theorem cover1LB : Cover (WeightedBound 2931) (child ⟨true,false,1⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF1LB.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF1LB.bound_all
theorem cover1LE : Cover (WeightedBound 2931) (child ⟨true,false,4⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF1LE.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF1LE.bound_all
theorem cover1RB : Cover (WeightedBound 2931) (child ⟨true,true,1⟩) :=
  transport (q := BB6.Agent7Raw124ZeroLF1RB.pChild) (by decide) (by decide)
    BB6.Agent7Raw124ZeroLF1RB.bound_all

def residualMoves : List Move := [⟨true,true,2⟩]
theorem residual_count : residualMoves.length = 1 := by decide
theorem parent_cut (m : Machine) (hm : compatible parent m) :
    WeightedBound 2931 m ∨ ∃ mv ∈ residualMoves, compatible (child mv) m := by
  rcases parent_dichotomy m hm with h | ⟨mv,hr,hc⟩
  · exact Or.inl (weighted_mono (by decide : 15 ≤ 2931) h)
  · rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    · exact False.elim ((by decide : ⟨false,false,0⟩ ∉ remaining) hr)
    · exact Or.inl (cover0RA.sound m hc)
    · exact Or.inl (cover1LA.sound m hc)
    · exact Or.inl (cover1RA.sound m hc)
    · exact False.elim ((by decide : ⟨false,false,1⟩ ∉ remaining) hr)
    · exact Or.inl (cover0RB.sound m hc)
    · exact Or.inl (cover1LB.sound m hc)
    · exact Or.inl (cover1RB.sound m hc)
    · exact False.elim ((by decide : ⟨false,false,2⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨false,true,2⟩ ∉ remaining) hr)
    · exact Or.inl (cover1LC.sound m hc)
    · exact Or.inr ⟨⟨true,true,2⟩,by decide,hc⟩
    · exact False.elim ((by decide : ⟨false,false,3⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨false,true,3⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨true,false,3⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨true,true,3⟩ ∉ remaining) hr)
    · exact Or.inl (cover0LE.sound m hc)
    · exact Or.inl (cover0RE.sound m hc)
    · exact Or.inl (cover1LE.sound m hc)
    · exact Or.inl (cover1RE.sound m hc)
    · exact False.elim ((by decide : ⟨false,false,5⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨false,true,5⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨true,false,5⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨true,true,5⟩ ∉ remaining) hr)

/-- Once the last child is proved, all completions of F1=0LF are covered. -/
theorem cover_of_last (B : Nat) (hB : 2931 ≤ B)
    (last : Cover (WeightedBound B) (child ⟨true,true,2⟩)) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases parent_cut m hm with h | ⟨mv, hmv, hc⟩
  · exact weighted_mono hB h
  · have he : mv = ⟨true,true,2⟩ := by simpa [residualMoves] using hmv
    subst mv
    exact last.sound m hc

#print axioms parent_cut
#print axioms cover_of_last
end BB6.Agent12Raw124ZeroLFAccepted
