import FastRootBackward
import FastArithmetic
import SectionBackwardFuelOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fast
open BB6.Agent46
open BB6.Agent11Mass
open BB6.Agent11BackwardFuel

/-- Pointwise matching predicates give exactly the same ordered candidate list,
    including multiplicities, without evaluating the source transition. -/
theorem arithmeticCandidates_eq (x y:Nat) (hy:5≤y) :
  arithmeticCandidates x y=fastCandidates x y := by
  have h:(fun p:Nat×Nat=>arithmeticValid p.1 p.2 x y) =
      (fun p:Nat×Nat=>decide (secNext p=some (x,y))) := by
    funext p
    rcases p with ⟨a,k⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      ((arithmeticValid_criterion a k x y hy).trans
       (complete_section_inverse a k x y hy).symm)
  simp only [arithmeticCandidates,fastCandidates,h]

/-- Arithmetic-only high targets; source-faithful primitive recursion handles
    the exceptional low-output states. -/
def arithmeticCandidatesAll (x y:Nat) : List (Nat×Nat) :=
  if 5≤y then arithmeticCandidates x y else sourceCandidatesFuel x y

theorem arithmeticCandidatesAll_eq (x y:Nat) :
 arithmeticCandidatesAll x y=fastCandidatesAll x y := by
  by_cases hy:5≤y
  · simp only [arithmeticCandidatesAll,fastCandidatesAll,if_pos hy,
      arithmeticCandidates_eq x y hy]
  · simp only [arithmeticCandidatesAll,fastCandidatesAll,if_neg hy,
      sourceCandidatesFuel_eq]

def backwardArithmetic : Nat → Nat×Nat → Bool
 | 0,p => decide (p=(5,1))
 | n+1,p => if p=(5,1) then true else
     (arithmeticCandidatesAll p.1 p.2).any (fun q=>backwardArithmetic n q)

theorem backwardArithmetic_eq (n:Nat) : ∀ p:Nat×Nat,
    backwardArithmetic n p=backwardFast n p := by
  induction n with
  | zero =>
      intro p
      rfl
  | succ n ih =>
      intro p
      by_cases hp:p=(5,1)
      · simp [backwardArithmetic,backwardFast,hp]
      · simp only [backwardArithmetic,backwardFast,if_neg hp,
          arithmeticCandidatesAll_eq,ih]

/-- Exact all-time blank-section reachability via bounded arithmetic-only
    high-output inverses and a finite low-output fallback. -/
theorem backwardArithmeticHalfFull_iff (x y:Nat) :
 backwardArithmetic ((x+2*y)/2) (x,y)=true ↔ SectionReach x y := by
  rw [backwardArithmetic_eq,backwardFastHalfFull_iff]

#print axioms arithmeticCandidates_eq
#print axioms backwardArithmeticHalfFull_iff
end BB6.Agent11Fast
