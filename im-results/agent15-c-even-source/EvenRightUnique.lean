import EvenEvenUnique
import OddEvenUnique
import SectionAffineInverse
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Every even-right return with right counter >=6 and total coordinate
    sum outside residues 0 and 7 modulo eight has exactly one genuine
    original-source predecessor, regardless of bounce recursion depth. -/
theorem section_even_right_iff_affine (a k x y : Nat)
    (hy : 6≤y) (heven : y%2=0)
    (hzero : (x+y)%8≠0) (hseven : (x+y)%8≠7) :
    secNext (a,k)=some (x,y) ↔
      a=x+y-2 ∧ k=(y-2)/2 := by
  by_cases hs : (x+y)%4=1
  · exact section_sum_one_even_iff_affine a k x y (by omega) heven hs
  · by_cases hx : x%2=0
    · exact section_even_even_iff_affine a k x y hx heven hy hzero
    · have hodd : x%2=1 := by omega
      have hthree : (x+y)%8=3 := by omega
      exact section_odd_even_iff_affine a k x y hodd heven hy hthree

/-- The unique predecessor preserves reachability equivalence from the
    actual blank section start, with no bounded-time approximation. -/
theorem blank_reach_iff_even_right (x y : Nat)
    (hy : 6≤y) (heven : y%2=0)
    (hzero : (x+y)%8≠0) (hseven : (x+y)%8≠7) :
    (∃ t : Nat, BB6.Agent8Section.run secNext t (some (5,1))=some (x,y)) ↔
    (∃ t : Nat, BB6.Agent8Section.run secNext t (some (5,1))=
        some (x+y-2,(y-2)/2)) := by
  constructor
  · rintro ⟨t,ht⟩
    cases t with
    | zero =>
        simp [BB6.Agent8Section.run] at ht
        omega
    | succ n =>
        cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hp] at ht
        | some p =>
            rcases p with ⟨a,k⟩
            have hstep : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using ht
            obtain ⟨ha,hk⟩ :=
              (section_even_right_iff_affine a k x y hy heven hzero hseven).mp hstep
            exact ⟨n,by rwa [ha,hk] at hp⟩
  · rintro ⟨t,ht⟩
    refine ⟨t+1,?_⟩
    have hstep : secNext (x+y-2,(y-2)/2)=some (x,y) :=
      (section_even_right_iff_affine _ _ x y hy heven hzero hseven).mpr ⟨rfl,rfl⟩
    simpa [BB6.Agent8Section.run,ht,hstep]

#print axioms section_even_right_iff_affine
#print axioms blank_reach_iff_even_right
end BB6.Agent15
