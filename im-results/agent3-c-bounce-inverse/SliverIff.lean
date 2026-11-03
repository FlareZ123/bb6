import OddSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Exact genuine source iff for the whole congruence wedge. -/
theorem odd_sliver_parent_iff (a k x y : Nat)
    (hx : x%8=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y) :
    secNext (a,k)=some (x,y) ↔
      x+y=2*a+4 ∧ x+3*y=4*k+10 := by
  constructor
  · exact odd_sliver_parent_equations a k x y hx hy hy5 hs hsize
  · rintro ⟨hsum,hcost⟩
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hlow : ¬2*k≤a := by omega
    have heven : a%2=0 := by omega
    apply (section_preimage_all_iff a k x y).mpr
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_pos heven]
    refine ⟨by omega,0,?_,?_⟩ <;> simp <;> omega

/-- Every point of the sliver has exactly one actual section predecessor. -/
theorem odd_sliver_unique_parent (x y : Nat)
    (hx : x%8=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y) :
    ∃ a k, secNext (a,k)=some (x,y) ∧
      ∀ b c, secNext (b,c)=some (x,y) → b=a ∧ c=k := by
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  have hsum : x+y=2*a+4 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+10 := by dsimp [k]; omega
  have hedge := (odd_sliver_parent_iff a k x y hx hy hy5 hs hsize).mpr ⟨hsum,hcost⟩
  refine ⟨a,k,hedge,?_⟩
  intro b c hbc
  have hh := (odd_sliver_parent_iff b c x y hx hy hy5 hs hsize).mp hbc
  omega

#print axioms odd_sliver_parent_iff
#print axioms odd_sliver_unique_parent
end BB6.Agent3
