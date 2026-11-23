import SourceCostModel

/-!
# Source-linked exact step-cost induction, conditional only on one-step cost soundness

The `stepPure` appearing in every statement is the actual pinned upstream
`BusyBeaver.SymRunEngine.stepPure` definition. The definitions are fully
transparent; neither `sorry` nor a postulated theorem is introduced.

The remaining `ExactSymStep` premise must eventually be instantiated from
F424/F412 machine-specific exact `execute n` witnesses. This file by itself
does not claim to discharge that premise.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BB6.Agent11.SourceCost

/-- The one-step exact-cost proof obligation for a particular concrete TM
    and F424/F412 rule-cost variant. The `evalSym` interpreter is original
    upstream code, not independently transcribed. -/
def ExactSymStep (M : Machine (Fin 2) (Fin 6)) (is424 : Bool) : Prop :=
  ∀ s : SymState,
    multiStep M (evalSym M s) (costPure is424 s) =
      some (evalSym M (stepPure s))

theorem costIter_zero (is424 : Bool) (s : SymState) :
    costIter is424 0 s = 0 := rfl

theorem costIter_succ (is424 : Bool) (n : Nat) (s : SymState) :
    costIter is424 (n+1) s =
      costPure is424 s + costIter is424 n (stepPure s) := rfl

/-- The exact candidate cost composes along the original source transition.
    This allows a 4096-step cost fold to be split at source checkpoints. -/
theorem costIter_add (is424 : Bool) (n m : Nat) (s : SymState) :
    costIter is424 (n+m) s =
      costIter is424 n s + costIter is424 m (iterStep stepPure n s) := by
  induction n generalizing s with
  | zero =>
    simp only [Nat.zero_add, costIter_zero, iterStep, Nat.zero_add]
  | succ n ih =>
    rw [Nat.succ_add, costIter_succ, costIter_succ, iterStep]
    rw [ih]
    omega

/-- Exact natural-number primitive-time reachability, provided every
    source `stepPure` transition's rule-specific count has been proved.
    It establishes an exact count, not a loose bound. -/
theorem costIter_exact_reaches
    {M : Machine (Fin 2) (Fin 6)} {is424 : Bool}
    (h : ExactSymStep M is424) (n : Nat) (s : SymState) :
    multiStep M (evalSym M s) (costIter is424 n s) =
      some (evalSym M (iterStep stepPure n s)) := by
  induction n generalizing s with
  | zero =>
    rfl
  | succ n ih =>
    change multiStep M (evalSym M s)
      (costPure is424 s + costIter is424 n (stepPure s)) =
        some (evalSym M (iterStep stepPure n (stepPure s)))
    exact multiStep_trans (h s) (ih (stepPure s))

/-- To accept a computed root-to-checkpoint exact cost, it suffices to
    close one global `ExactSymStep` premise and two decidable finite
    source computations (the trace endpoint and its accumulated count). -/
theorem costIter_exact_checkpoint
    {M : Machine (Fin 2) (Fin 6)} {is424 : Bool}
    (h : ExactSymStep M is424) (n : Nat)
    (s0 s1 : SymState) (primitiveCount : Nat)
    (hstate : iterStep stepPure n s0 = s1)
    (hcost : costIter is424 n s0 = primitiveCount) :
    multiStep M (evalSym M s0) primitiveCount =
      some (evalSym M s1) := by
  rw [← hcost, ← hstate]
  exact costIter_exact_reaches h n s0

#print axioms costIter_zero
#print axioms costIter_succ
#print axioms costIter_add
#print axioms costIter_exact_reaches
#print axioms costIter_exact_checkpoint

end BB6.Agent11.SourceCost
