import Agent3COneFamily
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Reachability from the genuine blank Machine C section of any (1,4*j)
    is equivalent to reachability of its explicit affine feeder. -/
def CReach (a k : Nat) : Prop :=
  ∃ time : Nat, BB6.Agent8Section.run secNext time (some (5,1)) = some (a,k)

theorem blank_one_four_iff_feeder (j : Nat) (hj : 1≤j) :
    CReach 1 (4*j) ↔ CReach (4*j-1) (2*j-1) := by
  constructor
  · rintro ⟨time,h⟩
    cases time with
    | zero => simp [BB6.Agent8Section.run] at h
    | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
        rcases p with ⟨a,k⟩
        have ht : secNext (a,k)=some (1,4*j) := by
          simpa [BB6.Agent8Section.run,hp] using h
        obtain ⟨ha,hk⟩ := (section_one_four_exact a k j hj).mp ht
        exact ⟨t,by rwa [ha,hk] at hp⟩
  · rintro ⟨time,h⟩
    refine ⟨time+1, ?_⟩
    have hs : secNext (4*j-1,2*j-1)=some (1,4*j) :=
      (section_one_four_exact _ _ _ hj).mpr ⟨rfl,rfl⟩
    simpa [BB6.Agent8Section.run,h,hs]

#print axioms blank_one_four_iff_feeder
end BB6.Agent3
