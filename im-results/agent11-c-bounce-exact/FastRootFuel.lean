import FastRootBackward
import SectionBackwardFuelOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fast
open BB6.Agent46
open BB6.Agent11Fuel
open BB6.Agent11BackwardFuel

/-- Structurally recursive exact section transition filtering of the
    logarithmic candidate list. -/
def fastCandidatesFuel (x y:Nat) : List (Nat×Nat) :=
  (fastUnfiltered x y).filter (fun p => secNextFuel p = some (x,y))

theorem fastCandidatesFuel_eq (x y:Nat) :
   fastCandidatesFuel x y = fastCandidates x y := by
  have h:(fun p:Nat×Nat => decide (secNextFuel p=some (x,y))) =
      (fun p:Nat×Nat => decide (secNext p=some (x,y))) := by
    funext p
    rcases p with ⟨a,k⟩
    rw [secNextFuel_eq a k]
  simp only [fastCandidatesFuel,fastCandidates,h]

def fastCandidatesAllFuel (x y:Nat) : List (Nat×Nat) :=
  if 5≤y then fastCandidatesFuel x y else sourceCandidatesFuel x y

theorem fastCandidatesAllFuel_eq (x y:Nat) :
    fastCandidatesAllFuel x y=fastCandidatesAll x y := by
  by_cases hy:5≤y
  · simp only [fastCandidatesAllFuel,fastCandidatesAll,if_pos hy,
      fastCandidatesFuel_eq]
  · simp only [fastCandidatesAllFuel,fastCandidatesAll,if_neg hy,
      sourceCandidatesFuel_eq]

/-- Entirely primitive recursive exact backward-root decision, with a
    logarithmic input candidate list at every high-output node. -/
def backwardFastFuel : Nat → Nat×Nat → Bool
 | 0,p => decide (p=(5,1))
 | n+1,p => if p=(5,1) then true
      else (fastCandidatesAllFuel p.1 p.2).any (fun q => backwardFastFuel n q)

theorem backwardFastFuel_eq (n:Nat) : ∀p:Nat×Nat,
    backwardFastFuel n p=backwardFast n p := by
  induction n with
  | zero =>
      intro p
      rfl
  | succ n ih =>
      intro p
      by_cases hp:p=(5,1)
      · simp [backwardFastFuel,backwardFast,hp]
      · simp only [backwardFastFuel,backwardFast,if_neg hp,
          fastCandidatesAllFuel_eq,ih]

/-- True blank-root Machine C section reachability for any fixed target,
    witnessed by a kernel-evaluable Boolean using the exact inverse grammar. -/
theorem backwardFastFuelHalfFull_iff (x y:Nat) :
    backwardFastFuel ((x+2*y)/2) (x,y)=true ↔
      BB6.Agent11Mass.SectionReach x y := by
  rw [backwardFastFuel_eq,backwardFastHalfFull_iff]

#print axioms fastCandidatesFuel_eq
#print axioms backwardFastFuelHalfFull_iff
end BB6.Agent11Fast
