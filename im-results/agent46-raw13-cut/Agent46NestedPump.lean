import Agent46AutoPumpN
namespace BB6Coverage.Agent31Pump.Nested
open BB6Coverage BB6Coverage.Agent31Pump

theorem rep_mul (w : List Bool) (k n : Nat) : rep (rep w k) n = rep w (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,Auto.rep_add,Nat.mul_succ]; congr 1; omega

/-- A general draining loop, with an untouched parameter j. -/
def drainCost (c : Nat → Nat → Nat → Nat) (k j : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => c k b j + drainCost c (k+1) j b

theorem drain (p : PartialMachine) (B : Nat → Nat → Nat → Z0)
    (c : Nat → Nat → Nat → Nat)
    (inner : ∀ k b j, run0 p (c k b j) (B k (b+1) j) = some (B (k+1) b j))
    (k b j : Nat) : run0 p (drainCost c k j b) (B k b j) = some (B (k+b) 0 j) := by
  induction b generalizing k with
  | zero => simp [drainCost,run0]
  | succ b ih =>
    rw [drainCost]
    have h := join0 (inner k b j) (ih (k+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

#print axioms rep_mul
#print axioms drain
end BB6Coverage.Agent31Pump.Nested
