import SectionRank
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

/-- Every actual blank-origin return at time n satisfies n+7 ≤ a+2*k.
    In particular the source-independent section rank is a strict clock. -/
theorem blank_rank_time (n a k : Nat)
    (h : BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) :
    n+7≤a+2*k := by
  induction n generalizing a k with
  | zero =>
    simp [BB6.Agent8Section.run] at h
    omega
  | succ n ih =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨u,v⟩
      have hs : secNext (u,v)=some (a,k) := by
        simpa [BB6.Agent8Section.run,hp] using h
      have hr := section_rank_strict u v a k hs
      have prev := ih u v hp
      omega

#print axioms blank_rank_time
end BB6.Agent3
