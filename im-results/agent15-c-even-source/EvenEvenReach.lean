import EvenEvenUnique
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- A fourth genuinely forced Machine C inverse region. Its exact
    predecessor is reachable from the blank section iff the target is. -/
theorem blank_reach_iff_even_even (x y : Nat)
    (hx : x%2=0) (hy : y%2=0) (h6 : 6≤y)
    (hs : (x+y)%8≠0) :
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
              (section_even_even_iff_affine a k x y hx hy h6 hs).mp hstep
            exact ⟨n,by rwa [ha,hk] at hp⟩
  · rintro ⟨t,ht⟩
    refine ⟨t+1,?_⟩
    have hstep : secNext (x+y-2,(y-2)/2)=some (x,y) :=
      (section_even_even_iff_affine _ _ x y hx hy h6 hs).mpr ⟨rfl,rfl⟩
    simpa [BB6.Agent8Section.run,ht,hstep]

#print axioms blank_reach_iff_even_even
end BB6.Agent15
