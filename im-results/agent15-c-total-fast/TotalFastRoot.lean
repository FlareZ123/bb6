import TotalFastInverse
import SectionMassOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15TotalFast
open BB6.Agent46 BB6.Agent8Section BB6.Agent11Mass

/-- Entirely logarithmic local inverse branching at every original section output. -/
def backwardTotal : Nat → Nat × Nat → Bool
 | 0,p => decide (p=(5,1))
 | n+1,p => if p=(5,1) then true
     else (totalFastCandidates p.1 p.2).any (fun q => backwardTotal n q)

theorem backwardTotal_iff (fuel : Nat) : ∀ p : Nat × Nat,
  backwardTotal fuel p = true ↔
    ∃ n ≤ fuel, run secNext n (some (5,1)) = some p := by
  induction fuel with
  | zero =>
    intro p
    simp only [backwardTotal, decide_eq_true_eq]
    constructor
    · intro hp
      subst p
      exact ⟨0,by omega,rfl⟩
    · rintro ⟨n,hn,h⟩
      have hn0 : n=0 := by omega
      subst n
      simp only [BB6.Agent8Section.run,Option.some.injEq] at h
      exact h.symm
  | succ fuel ih =>
    intro p
    by_cases hroot : p=(5,1)
    · simp only [backwardTotal,if_pos hroot]
      constructor
      · intro _
        subst p
        exact ⟨0,by omega,rfl⟩
      · intro _
        trivial
    · simp only [backwardTotal,if_neg hroot,List.any_eq_true]
      constructor
      · rintro ⟨q,hmem,hq⟩
        obtain ⟨n,hn,htrace⟩ := (ih q).mp hq
        have hnext : secNext q=some p := by
          have hh := (totalFastCandidates_exact q.1 q.2 p.1 p.2).mp hmem
          simpa using hh
        refine ⟨n+1,by omega,?_⟩
        change (run secNext n (some (5,1))).bind secNext=some p
        rw [htrace]
        exact hnext
      · rintro ⟨n,hn,htrace⟩
        cases n with
        | zero =>
          have hp:p=(5,1) := by
            simp only [BB6.Agent8Section.run,Option.some.injEq] at htrace
            exact htrace.symm
          exact False.elim (hroot hp)
        | succ n =>
          change (run secNext n (some (5,1))).bind secNext=some p at htrace
          cases hp : run secNext n (some (5,1)) with
          | none => simp [hp] at htrace
          | some q =>
            have hnext:secNext q=some p := by simpa [hp] using htrace
            have hmem : q∈totalFastCandidates p.1 p.2 := by
              apply (totalFastCandidates_exact q.1 q.2 p.1 p.2).mpr
              simpa using hnext
            have hq:backwardTotal fuel q=true :=
              (ih q).mpr ⟨n,by omega,hp⟩
            exact ⟨q,hmem,hq⟩

/-- Full blank-root decision for each fixed original Machine C section target. -/
theorem backwardTotalHalfFull_iff (x y : Nat) :
    backwardTotal ((x+2*y)/2) (x,y)=true ↔ SectionReach x y := by
  rw [backwardTotal_iff,section_reach_iff_half_bound]

#print axioms backwardTotal_iff
#print axioms backwardTotalHalfFull_iff
end BB6.Agent15TotalFast
