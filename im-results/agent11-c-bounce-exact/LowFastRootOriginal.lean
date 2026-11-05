import LowFastCandidatesOriginal
import FastArithmeticRoot
import SectionBackwardFuelOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fast
open BB6.Agent46
open BB6.Agent11Fuel
open BB6.Agent11Mass
open BB6.Agent11BackwardFuel
open BB6.Agent8Section

def allLowFastCandidates (x y:Nat) : List (Nat×Nat) :=
  if 5≤y then arithmeticCandidates x y
  else if y=3 then (lowThreeList x).filter (fun p => secNextFuel p=some (x,y))
  else if y=4 then (lowFourList x).filter (fun p => secNextFuel p=some (x,y))
  else sourceCandidatesFuel x y

theorem allLowFastCandidates_exact (a k x y:Nat) :
 (a,k)∈allLowFastCandidates x y ↔ secNext (a,k)=some (x,y) := by
  by_cases hbig:5≤y
  · simpa only [allLowFastCandidates,if_pos hbig] using
      (arithmeticCandidates_exact a k x y hbig)
  · by_cases h3:y=3
    · subst y
      have hn:¬5≤3 := by decide
      simp only [allLowFastCandidates,if_neg hn,if_pos rfl,
          List.mem_filter,decide_eq_true_eq]
      constructor
      · intro h
        rcases h with ⟨_,hh⟩
        simpa only [secNextFuel_eq] using hh
      · intro h
        refine ⟨lowThreeComplete a k x h,?_⟩
        simpa only [secNextFuel_eq] using h
    · by_cases h4:y=4
      · subst y
        have hn:¬5≤4 := by decide
        have h3':4≠3 := by decide
        simp only [allLowFastCandidates,if_neg hn,if_neg h3',if_pos rfl,
            List.mem_filter,decide_eq_true_eq]
        constructor
        · intro h
          rcases h with ⟨_,hh⟩
          simpa only [secNextFuel_eq] using hh
        · intro h
          refine ⟨lowFourComplete a k x h,?_⟩
          simpa only [secNextFuel_eq] using h
      · simpa only [allLowFastCandidates,if_neg hbig,if_neg h3,if_neg h4,
          sourceCandidatesFuel_eq] using (sourceCandidates_correct a k x y)

def backwardAllLowFast : Nat → Nat×Nat → Bool
 | 0,p => decide (p=(5,1))
 | n+1,p => if p=(5,1) then true else
       (allLowFastCandidates p.1 p.2).any (fun q=>backwardAllLowFast n q)

theorem backwardAllLowFast_iff (fuel:Nat) : ∀p:Nat×Nat,
 backwardAllLowFast fuel p=true ↔
    ∃n≤fuel,run secNext n (some (5,1))=some p := by
  induction fuel with
  | zero =>
      intro p
      simp only [backwardAllLowFast,decide_eq_true_eq]
      constructor
      · intro hp
        subst p
        exact ⟨0,by omega,rfl⟩
      · rintro ⟨n,hn,h⟩
        have hn0:n=0:=by omega
        subst n
        simp only [BB6.Agent8Section.run,Option.some.injEq] at h
        exact h.symm
  | succ fuel ih =>
      intro p
      by_cases hroot:p=(5,1)
      · simp only [backwardAllLowFast,if_pos hroot]
        constructor
        · intro _
          subst p
          exact ⟨0,by omega,rfl⟩
        · intro _
          trivial
      · simp only [backwardAllLowFast,if_neg hroot,List.any_eq_true]
        constructor
        · rintro ⟨q,hmem,hq⟩
          obtain ⟨n,hn,htrace⟩ := (ih q).mp hq
          have hnext:secNext q=some p := by
            have hm:=(allLowFastCandidates_exact q.1 q.2 p.1 p.2).mp hmem
            simpa using hm
          refine ⟨n+1,by omega,?_⟩
          change (run secNext n (some (5,1))).bind secNext=some p
          rw [htrace]
          exact hnext
        · rintro ⟨n,hn,htrace⟩
          cases n with
          | zero =>
              have hp:p=(5,1):=by
                simp only [BB6.Agent8Section.run,Option.some.injEq] at htrace
                exact htrace.symm
              exact False.elim (hroot hp)
          | succ n =>
              change (run secNext n (some (5,1))).bind secNext=some p at htrace
              cases hp:run secNext n (some (5,1)) with
              | none => simp [hp] at htrace
              | some q =>
                  have hnext:secNext q=some p:=by simpa [hp] using htrace
                  have hmem:q∈allLowFastCandidates p.1 p.2 :=
                    (allLowFastCandidates_exact q.1 q.2 p.1 p.2).mpr
                      (by simpa using hnext)
                  have hq:backwardAllLowFast fuel q=true:=
                    (ih q).mpr ⟨n,by omega,hp⟩
                  exact ⟨q,hmem,hq⟩

theorem backwardAllLowFastFull_iff (x y:Nat) :
 backwardAllLowFast ((x+2*y)/2) (x,y)=true ↔ SectionReach x y := by
  rw [backwardAllLowFast_iff,section_reach_iff_half_bound]

#print axioms backwardAllLowFastFull_iff

#print axioms allLowFastCandidates_exact
end BB6.Agent11Fast
