import SectionBackwardOriginal
import SectionFuelOriginal
import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11BackwardFuel
open BB6.Agent46
open BB6.Agent11Fuel
open BB6.Agent11Backward
open BB6.Agent11Mass

def sourceCandidatesFuel (x y : Nat) : List (Nat × Nat) :=
  let bound := x+2*y+1
  ((List.range bound).flatMap
    (fun a => (List.range bound).map (fun k => (a,k)))).filter
    (fun p => decide (secNextFuel p = some (x,y)))

theorem sourceCandidatesFuel_eq (x y : Nat) :
    sourceCandidatesFuel x y = sourceCandidates x y := by
  have h : (fun (p : Nat×Nat) => decide (secNextFuel p=some (x,y))) =
      (fun (p : Nat×Nat) => decide (secNext p=some (x,y))) := by
    funext p
    rcases p with ⟨a,k⟩
    rw [secNextFuel_eq a k]
  simp only [sourceCandidatesFuel,sourceCandidates,h]

def backwardHitFuel : Nat → Nat × Nat → Bool
  | 0,p => decide (p=(5,1))
  | n+1,p =>
      if p=(5,1) then true
      else (sourceCandidatesFuel p.1 p.2).any (fun q => backwardHitFuel n q)

theorem backwardHitFuel_eq (n : Nat) : ∀p : Nat×Nat,
    backwardHitFuel n p = backwardHit n p := by
  induction n with
  | zero =>
      intro p
      rfl
  | succ n ih =>
      intro p
      by_cases hp : p=(5,1)
      · simp [backwardHitFuel,backwardHit,hp]
      · simp only [backwardHitFuel,backwardHit,if_neg hp,
          sourceCandidatesFuel_eq,ih]

theorem backwardHitFuelFull_iff (x y:Nat) :
    backwardHitFuel (x+2*y) (x,y)=true ↔ SectionReach x y := by
  rw [backwardHitFuel_eq, backwardFull_iff]


theorem backwardHitFuelHalfFull_iff (x y : Nat) :
  backwardHitFuel ((x+2*y)/2) (x,y)=true ↔ SectionReach x y := by
  rw [backwardHitFuel_eq, backwardHalfFull_iff]

#print axioms backwardHitFuelHalfFull_iff

#print axioms sourceCandidatesFuel_eq
#print axioms backwardHitFuel_eq
#print axioms backwardHitFuelFull_iff

end BB6.Agent11BackwardFuel
