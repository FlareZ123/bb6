import Raw124ZeroLFParent
import Raw124ZeroLF0LE
import Raw124ZeroLF0RB
import Raw124ZeroLF0RE
import Raw124ZeroLF1LC
import Raw124ZeroLF1RA
import Raw124ZeroLF1RE
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

def residualMoves : List Move := [⟨false,true,0⟩,⟨true,false,0⟩,⟨true,false,1⟩,⟨true,false,4⟩,⟨true,true,1⟩,⟨true,true,2⟩]
theorem residual_count : residualMoves.length = 6 := by decide
theorem parent_cut (m : Machine) (hm : compatible parent m) :
    WeightedBound 2931 m ∨ ∃ mv ∈ residualMoves, compatible (child mv) m := by
  rcases parent_dichotomy m hm with h | ⟨mv,hr,hc⟩
  · exact Or.inl (weighted_mono (by decide : 15 ≤ 2931) h)
  · rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    · exact False.elim ((by decide : ⟨false,false,0⟩ ∉ remaining) hr)
    · exact Or.inr ⟨⟨false,true,0⟩,by decide,hc⟩
    · exact Or.inr ⟨⟨true,false,0⟩,by decide,hc⟩
    · exact Or.inl (cover1RA.sound m hc)
    · exact False.elim ((by decide : ⟨false,false,1⟩ ∉ remaining) hr)
    · exact Or.inl (cover0RB.sound m hc)
    · exact Or.inr ⟨⟨true,false,1⟩,by decide,hc⟩
    · exact Or.inr ⟨⟨true,true,1⟩,by decide,hc⟩
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
    · exact Or.inr ⟨⟨true,false,4⟩,by decide,hc⟩
    · exact Or.inl (cover1RE.sound m hc)
    · exact False.elim ((by decide : ⟨false,false,5⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨false,true,5⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨true,false,5⟩ ∉ remaining) hr)
    · exact False.elim ((by decide : ⟨true,true,5⟩ ∉ remaining) hr)

#print axioms parent_cut
end BB6.Agent12Raw124ZeroLFAccepted
