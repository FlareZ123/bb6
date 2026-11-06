import ValuationTwoAdicSplit
import TotalFastRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46 BB6.Agent8Section BB6.Agent15TotalFast

/-- Replace the generic logarithmic inverse list by the sharper
valuation-indexed exact list whenever y>=5. Keep the established exact
small-y oracle for the remaining boundary cases. -/
def totalFastCandidatesValuation (x y : Nat) : List (Nat × Nat) :=
  if 5≤y then valuationFullCandidates x y
  else BB6.Agent15TotalFast.totalFastCandidates x y

theorem totalFastCandidatesValuation_exact (x y a k : Nat) :
    (a,k)∈totalFastCandidatesValuation x y ↔
      secNext (a,k)=some (x,y) := by
  by_cases hy : 5≤y
  · simp [totalFastCandidatesValuation,hy,valuationFullCandidates_exact]
  · simp [totalFastCandidatesValuation,hy,
      BB6.Agent15TotalFast.totalFastCandidates_exact]

/-- Same bounded backward reachability recursion as Agent 15, using
the smaller valuation-indexed exact predecessor list for y>=5. -/
def backwardTotalValuation : Nat → Nat × Nat → Bool
 | 0,p => decide (p=(5,1))
 | n+1,p => if p=(5,1) then true
     else (totalFastCandidatesValuation p.1 p.2).any
       (fun q => backwardTotalValuation n q)

theorem backwardTotalValuation_iff (fuel : Nat) : ∀ p : Nat × Nat,
  backwardTotalValuation fuel p = true ↔
    ∃ n ≤ fuel, run secNext n (some (5,1)) = some p := by
  induction fuel with
  | zero =>
    intro p
    simp only [backwardTotalValuation,decide_eq_true_eq]
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
    · simp only [backwardTotalValuation,if_pos hroot]
      constructor
      · intro _
        subst p
        exact ⟨0,by omega,rfl⟩
      · intro _
        trivial
    · simp only [backwardTotalValuation,if_neg hroot,List.any_eq_true]
      constructor
      · rintro ⟨q,hmem,hq⟩
        obtain ⟨n,hn,htrace⟩ := (ih q).mp hq
        have hnext : secNext q=some p := by
          have hh := (totalFastCandidatesValuation_exact
            q.1 q.2 p.1 p.2).mp hmem
          simpa using hh
        refine ⟨n+1,by omega,?_⟩
        change (run secNext n (some (5,1))).bind secNext=some p
        rw [htrace]
        exact hnext
      · rintro ⟨n,hn,htrace⟩
        cases n with
        | zero =>
          have hp : p=(5,1) := by
            simp only [BB6.Agent8Section.run,Option.some.injEq] at htrace
            exact htrace.symm
          exact False.elim (hroot hp)
        | succ n =>
          change (run secNext n (some (5,1))).bind secNext=some p at htrace
          cases hp : run secNext n (some (5,1)) with
          | none => simp [hp] at htrace
          | some q =>
            have hnext : secNext q=some p := by simpa [hp] using htrace
            have hmem : q∈totalFastCandidatesValuation p.1 p.2 := by
              apply (totalFastCandidatesValuation_exact
                q.1 q.2 p.1 p.2).mpr
              simpa using hnext
            have hq : backwardTotalValuation fuel q=true :=
              (ih q).mpr ⟨n,by omega,hp⟩
            exact ⟨q,hmem,hq⟩

/-- The sharper inverse oracle computes the same exact blank-root
reachability predicate as the established total-fast search. -/
theorem backwardTotalValuationHalfFull_iff (x y : Nat) :
    backwardTotalValuation ((x+2*y)/2) (x,y)=true ↔ SectionReach x y := by
  rw [backwardTotalValuation_iff,section_reach_iff_half_bound]

#print axioms totalFastCandidatesValuation_exact
#print axioms backwardTotalValuation_iff
#print axioms backwardTotalValuationHalfFull_iff

end BB6.Agent34Valuation
