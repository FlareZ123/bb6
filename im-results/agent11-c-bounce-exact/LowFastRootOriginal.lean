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

#print axioms allLowFastCandidates_exact
end BB6.Agent11Fast
