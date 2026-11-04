import SectionMassOriginal
import FastSectionDef
import GenericSection
import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Backward
open BB6.Agent46
open BB6.Agent8Section
open BB6.Agent11Mass

def backwardHit : Nat → Nat × Nat → Bool
 | 0,p => decide (p=(5,1))
 | n+1,p => if p=(5,1) then true
     else (sourceCandidates p.1 p.2).any (fun q => backwardHit n q)

theorem backwardHit_iff (fuel : Nat) : ∀ p : Nat × Nat,
  backwardHit fuel p = true ↔
    ∃ n ≤ fuel, run secNext n (some (5,1)) = some p := by
  induction fuel with
  | zero =>
    intro p
    simp only [backwardHit, decide_eq_true_eq]
    constructor
    · intro hp
      subst p
      exact ⟨0, by omega, rfl⟩
    · rintro ⟨n,hn,h⟩
      have hn0 : n=0 := by omega
      subst n
      simp only [run, Option.some.injEq] at h
      exact h.symm
  | succ fuel ih =>
    intro p
    by_cases hroot : p=(5,1)
    · simp only [backwardHit, if_pos hroot]
      constructor
      · intro _
        subst p
        exact ⟨0,by omega,rfl⟩
      · intro _
        trivial
    · simp only [backwardHit, if_neg hroot, List.any_eq_true]
      constructor
      · rintro ⟨q,hmem,hq⟩
        obtain ⟨n,hn,htrace⟩ := (ih q).mp hq
        have hnext : secNext q = some p := by
          have hm := (sourceCandidates_correct q.1 q.2 p.1 p.2).mp hmem
          simpa using hm
        refine ⟨n+1,by omega,?_⟩
        change (run secNext n (some (5,1))).bind secNext = some p
        rw [htrace]
        exact hnext
      · rintro ⟨n,hn,htrace⟩
        cases n with
        | zero =>
          have hp : p=(5,1) := by
            simp only [run, Option.some.injEq] at htrace
            exact htrace.symm
          exact False.elim (hroot hp)
        | succ n =>
          change (run secNext n (some (5,1))).bind secNext = some p at htrace
          cases hp : run secNext n (some (5,1)) with
          | none => simp [hp] at htrace
          | some q =>
            have hnext : secNext q = some p := by
              simpa [hp] using htrace
            have hmem : q ∈ sourceCandidates p.1 p.2 := by
              apply (sourceCandidates_correct q.1 q.2 p.1 p.2).mpr
              simpa using hnext
            have hq : backwardHit fuel q = true :=
              (ih q).mpr ⟨n,by omega,hp⟩
            exact ⟨q,hmem,hq⟩

theorem backwardFull_iff (x y : Nat) :
  backwardHit (x+2*y) (x,y) = true ↔ SectionReach x y := by
  rw [backwardHit_iff, section_reach_iff_bounded]

#print axioms backwardHit_iff
#print axioms backwardFull_iff
end BB6.Agent11Backward
