import SectionFastInverseOriginal
import SectionMassOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fast
open BB6.Agent46
open BB6.Agent8Section
open BB6.Agent11Mass

/-- Retain the finite low-output oracle; high outputs use the complete
    logarithmic inverse enumerator. -/
def fastCandidatesAll (x y:Nat) : List (Nat×Nat) :=
  if 5≤y then fastCandidates x y else sourceCandidates x y

theorem fastCandidatesAll_exact (a k x y:Nat) :
   (a,k)∈fastCandidatesAll x y ↔ secNext (a,k)=some (x,y) := by
  by_cases hy:5≤y
  · simpa only [fastCandidatesAll,if_pos hy] using fastCandidates_exact a k x y hy
  · simpa only [fastCandidatesAll,if_neg hy] using
      (sourceCandidates_correct a k x y)

/-- An exact backward root decision, using the section map on only
    logarithmically many candidates at each high-output node. -/
def backwardFast : Nat → Nat × Nat → Bool
 | 0,p => decide (p=(5,1))
 | n+1,p => if p=(5,1) then true
     else (fastCandidatesAll p.1 p.2).any (fun q => backwardFast n q)

theorem backwardFast_iff (fuel : Nat) : ∀ p : Nat × Nat,
  backwardFast fuel p = true ↔
    ∃ n ≤ fuel, run secNext n (some (5,1)) = some p := by
  induction fuel with
  | zero =>
    intro p
    simp only [backwardFast, decide_eq_true_eq]
    constructor
    · intro hp
      subst p
      exact ⟨0, by omega, rfl⟩
    · rintro ⟨n,hn,h⟩
      have hn0 : n=0 := by omega
      subst n
      simp only [BB6.Agent8Section.run, Option.some.injEq] at h
      exact h.symm
  | succ fuel ih =>
    intro p
    by_cases hroot : p=(5,1)
    · simp only [backwardFast, if_pos hroot]
      constructor
      · intro _
        subst p
        exact ⟨0,by omega,rfl⟩
      · intro _
        trivial
    · simp only [backwardFast, if_neg hroot, List.any_eq_true]
      constructor
      · rintro ⟨q,hmem,hq⟩
        obtain ⟨n,hn,htrace⟩ := (ih q).mp hq
        have hnext : secNext q = some p := by
          have hm := (fastCandidatesAll_exact q.1 q.2 p.1 p.2).mp hmem
          simpa using hm
        refine ⟨n+1,by omega,?_⟩
        change (run secNext n (some (5,1))).bind secNext = some p
        rw [htrace]
        exact hnext
      · rintro ⟨n,hn,htrace⟩
        cases n with
        | zero =>
          have hp : p=(5,1) := by
            simp only [BB6.Agent8Section.run, Option.some.injEq] at htrace
            exact htrace.symm
          exact False.elim (hroot hp)
        | succ n =>
          change (run secNext n (some (5,1))).bind secNext = some p at htrace
          cases hp : run secNext n (some (5,1)) with
          | none => simp [hp] at htrace
          | some q =>
            have hnext : secNext q = some p := by
              simpa [hp] using htrace
            have hmem : q ∈ fastCandidatesAll p.1 p.2 := by
              apply (fastCandidatesAll_exact q.1 q.2 p.1 p.2).mpr
              simpa using hnext
            have hq : backwardFast fuel q = true :=
              (ih q).mpr ⟨n,by omega,hp⟩
            exact ⟨q,hmem,hq⟩

/-- All-time blank-section reachability is equivalent to a finite backward
    search; the fuel derives from the original section mass inequality. -/
theorem backwardFastHalfFull_iff (x y : Nat) :
    backwardFast ((x+2*y)/2) (x,y)=true ↔ SectionReach x y := by
  rw [backwardFast_iff, section_reach_iff_half_bound]

#print axioms fastCandidatesAll_exact
#print axioms backwardFastHalfFull_iff
end BB6.Agent11Fast
