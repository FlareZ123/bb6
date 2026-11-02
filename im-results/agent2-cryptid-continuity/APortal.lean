import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 5000000
namespace BB6.CryptidPortal
open CryptidBoundary

/-- Alternating 01 cells to the left of the head, nearest first. -/
def left01 : Nat → List Bool
  | 0 => []
  | n+1 => [false,true] ++ left01 n

/-- Alternating 10 cells to the right of the head. -/
def right10 : Nat → List Bool
  | 0 => []
  | n+1 => [true,false] ++ right10 n

theorem right10_append_one (q : Nat) :
    right10 q ++ [true,false] = right10 (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change ([true,false] ++ right10 q) ++ [true,false] =
      [true,false] ++ right10 (q+1)
    rw [List.append_assoc, ih]

/-- Four actual D-start transitions convert one 01 pair on the left
    into a 10 pair to the right of the first right-hand 1. -/
theorem portal_one (L ys : List Bool) :
    run 4 (⟨[false,true] ++ L, true, true::ys, 0⟩ : Cfg) =
      ⟨L,true,true :: ([true,false] ++ ys),0⟩ := by
  simp [run, step, goL, goR]

def portal (q : Nat) (L ys : List Bool) : Cfg :=
  ⟨left01 q ++ L, true, true::ys, 0⟩

/-- Arbitrarily many 01 left pairs are converted exactly into 10 right
    pairs in 4q raw steps, for any left tail and arbitrary right suffix. -/
theorem portal_run (q : Nat) (L ys : List Bool) :
    run (4*q) (portal q L ys) =
      ⟨L,true,true::(right10 q ++ ys),0⟩ := by
  induction q generalizing ys with
  | zero => simp [portal,left01,right10,run]
  | succ q ih =>
    have ht : 4*(q+1) = 4+(4*q) := by omega
    rw [ht, run_add]
    change run (4*q) (run 4
      (⟨[false,true] ++ (left01 q ++ L), true, true::ys, 0⟩ : Cfg)) = _
    rw [portal_one]
    change run (4*q) (portal q L ([true,false] ++ ys)) = _
    rw [ih]
    have htail : right10 q ++ ([true,false] ++ ys) =
        right10 (q+1) ++ ys := by
      rw [← List.append_assoc, right10_append_one]
    exact congrArg (fun r : List Bool => Cfg.mk L true (true::r) 0) htail

#print axioms portal_one
#print axioms portal_run
end BB6.CryptidPortal
