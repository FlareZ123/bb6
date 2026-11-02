import SectionAffineInverse
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Every sum-one even-high Machine C section reachability question
    is exactly equivalent to reaching its one affine predecessor. -/
theorem blank_reach_iff_affine (x y : Nat)
    (hy : 4≤y) (heven : y%2=0) (hs : (x+y)%4=1) :
    (∃ time : Nat, BB6.Agent8Section.run secNext time (some (5,1))=some (x,y)) ↔
    (∃ time : Nat, BB6.Agent8Section.run secNext time (some (5,1))=
       some (x+y-2,(y-2)/2)) := by
  constructor
  · rintro ⟨time,h⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at h
        omega
    | succ t =>
        cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hp] at h
        | some p =>
            rcases p with ⟨a,k⟩
            have ht : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using h
            obtain ⟨ha,hk⟩ :=
              (section_sum_one_even_iff_affine a k x y hy heven hs).mp ht
            exact ⟨t,by rwa [ha,hk] at hp⟩
  · rintro ⟨time,h⟩
    refine ⟨time+1,?_⟩
    have ht : secNext (x+y-2,(y-2)/2)=some (x,y) :=
      (section_sum_one_even_iff_affine _ _ x y hy heven hs).mpr ⟨rfl,rfl⟩
    simpa [BB6.Agent8Section.run,h,ht]

#print axioms blank_reach_iff_affine
end BB6.Agent15
