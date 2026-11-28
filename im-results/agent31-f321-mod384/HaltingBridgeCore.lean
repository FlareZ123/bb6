import SourceHaltingBridge
import Lean.Elab.Tactic.Omega

/-!
A generic exact bridge from option-valued Collatz halting to the
finite reachability relation used by the F321 source-counter theorem.
Kept independent of upstream Cryptids / Mathlib so the theorem can
be reused with other original-machine accelerations.
-/
namespace BB6.Agent31F321Physical
open BB6.Agent31F321Density

/-- Exact option-valued nonhalting trace, maintaining its final state. -/
inductive OptTrace {S : Type} (f : S → Option S) (s : S) : Nat → S → Prop where
 | nil : OptTrace f s 0 s
 | step {m : Nat} {a b : S}
   (ha : OptTrace f s m a) (hb : f a = some b) :
   OptTrace f s (m+1) b

/-- Prepending a genuine option-valued move to an exact trace. -/
theorem OptTrace.prepend {S : Type} {f : S → Option S}
    {s s' t : S} {m : Nat} (h0 : f s = some s')
    (hr : OptTrace f s' m t) : OptTrace f s (m+1) t := by
  induction hr with
  | nil => exact OptTrace.step OptTrace.nil h0
  | @step n a b hr hab ih =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc]
        using (OptTrace.step ih hab)

/-- SourceNext is extended from pairs to a one-argument Option map. -/
def pairSourceNext : Nat × Nat → Option (Nat × Nat)
 | (a,d) => sourceNext a d

/-- Convert exact generic Option traces back to the already kernel-checked
    CounterReach semantics. -/
theorem source_trace_counter {m : Nat} {p : Nat × Nat}
    (hr : OptTrace pairSourceNext (1,1) m p) :
    CounterReach 1 1 m p.1 p.2 := by
  induction hr with
  | nil => exact CounterReach.nil
  | @step n a b hr hs ih =>
      rcases a with ⟨a,d⟩
      rcases b with ⟨A,D⟩
      exact CounterReach.step (by simpa using ih)
        (move_of_sourceNext_some (by simpa [pairSourceNext] using hs))

#print axioms source_trace_counter
end BB6.Agent31F321Physical
