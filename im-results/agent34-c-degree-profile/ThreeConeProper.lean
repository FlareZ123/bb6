import ThreeConeSource
import FastSectionDef
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34ThreeProper
open BB6.Agent46

/-- Every sufficiently high target with even right counter has the
canonical affine direct predecessor. This is an authentic original
section edge, not an abstract inverse grammar. -/
theorem direct_predecessor (x y : Nat)
    (hy : 6≤y) (he : y%2=0) :
    secNext (x+y-2,(y-2)/2)=some (x,y) := by
  let a := x+y-2
  let k := (y-2)/2
  have ha0 : a≠0 := by dsimp [a]; omega
  have ha1 : a≠1 := by dsimp [a]; omega
  have hk0 : k≠0 := by dsimp [k]; omega
  have hlow : 2*k≤a := by dsimp [a,k]; omega
  have hx : a-2*k=x := by dsimp [a,k]; omega
  have hy' : 2*k+2=y := by dsimp [k]; omega
  change secNext (a,k)=some (x,y)
  simp only [secNext,exactSection,if_neg ha0,if_neg ha1,
    if_neg hk0,if_pos hlow]
  rw [hx,hy']

/-- The whole y=2 mod 4 sector, at y>=14, is in the genuine two-step
image of the exact Machine C first-return section map. -/
theorem in_two_step_image (x y : Nat)
    (hy : 14≤y) (he : y%4=2) :
    ∃ a k b l,
       secNext (b,l)=some (a,k) ∧
       secNext (a,k)=some (x,y) := by
  let a := x+y-2
  let k := (y-2)/2
  let b := a+k-2
  let l := (k-2)/2
  have hk : 6≤k := by dsimp [k]; omega
  have hke : k%2=0 := by dsimp [k]; omega
  have hfirst : secNext (a,k)=some (x,y) := by
    simpa [a,k] using direct_predecessor x y (by omega) (by omega)
  have hsecond : secNext (b,l)=some (a,k) := by
    simpa [b,l] using direct_predecessor a k hk hke
  exact ⟨a,k,b,l,hsecond,hfirst⟩

/-- Strictly two-step but never three-step: a source-verified infinite
two-dimensional sector of positive asymptotic density 1/64. -/
theorem exactly_two_not_three (x y : Nat)
    (hy : 34≤y)
    (hsector : ((x+y)%8=1 ∧ y%16=10) ∨
               ((x+y)%8=3 ∧ y%16=2)) :
    (∃ a k b l, secNext (b,l)=some (a,k) ∧
       secNext (a,k)=some (x,y)) ∧
    (∀ u v b l a k, ¬ (secNext (u,v)=some (b,l) ∧
       secNext (b,l)=some (a,k) ∧ secNext (a,k)=some (x,y))) := by
  have hmod : y%4=2 := by omega
  refine ⟨in_two_step_image x y (by omega) hmod,?_⟩
  intro u v b l a k ⟨hthird,hsecond,hfirst⟩
  exact BB6.Agent34Three.no_three_edges u v b l a k x y hy hsector
    hthird hsecond hfirst

#print axioms direct_predecessor
#print axioms in_two_step_image
#print axioms exactly_two_not_three
end BB6.Agent34ThreeProper
