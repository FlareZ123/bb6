import TotalFastRoot
import BlankMassFour
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15TotalFast
open BB6.Agent46 BB6.Agent11Mass

/-- A sharp global quarter-mass fuel for the complete logarithmic-branching
    original source root oracle. The genuine blank trajectory has positive
    right counter at every step; its weighted mass grows by at least four. -/
theorem backwardTotalQuarterFull_iff (x y:Nat) :
    backwardTotal ((x+2*y-7)/4) (x,y)=true ↔ SectionReach x y := by
  rw [backwardTotal_iff]
  constructor
  · rintro ⟨n,_,h⟩
    exact ⟨n,h⟩
  · rintro ⟨n,h⟩
    have hb := BB6.Agent1ForwardMass.blank_section_index_upper n x y h
    exact ⟨n,hb,h⟩

#print axioms backwardTotalQuarterFull_iff
end BB6.Agent15TotalFast
