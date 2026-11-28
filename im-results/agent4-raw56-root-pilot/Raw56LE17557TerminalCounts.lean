import Lean.Elab.Tactic.Omega

/-!
  A proof of the terminal-one-run event counts in the **abstract** 17557
  triad substitution. At an A/B-triad boundary, assuming the right-hand
  one-run count changes by A:-1/B:+1 without zero-run coalescence, define
  height = (# finite right one-runs) - 2.

  A final third one-run occurs exactly when A starts at height 1.
  A final second one-run occurs exactly when B starts at height 0.
  The substitution A→ABA, B→BBA transforms these event counts by
  (finalA,finalB) ↦ (2*finalA,finalA+finalB).

  Crucially the scan below is *partial*: A at height zero returns none
  rather than saturating. This makes the substitution intertwining exact
  for every word and avoids an unproved positivity assumption.

  The theorem proves a combinatorial property of the substituted word;
  it does NOT claim that the original infinite blank orbit realizes that
  substitution or avoids all zero-run mergers. Those remain the genuine
  physical-machine synchronization obligations.
-/

namespace BB6.Agent4Raw56LE17557TerminalCounts

inductive Letter | a | b deriving Repr, DecidableEq

structure Scan where
  height : Nat
  finalA : Nat
  finalB : Nat
  deriving Repr, DecidableEq

def step : Letter → Scan → Option Scan
  | .a, ⟨0, _, _⟩ => none
  | .a, ⟨h+1, fa, fb⟩ =>
      some ⟨h, fa + (if h = 0 then 1 else 0), fb⟩
  | .b, ⟨h, fa, fb⟩ =>
      some ⟨h+1, fa, fb + (if h = 0 then 1 else 0)⟩

def exec : List Letter → Scan → Option Scan
  | [], s => some s
  | x::xs, s => (step x s).bind (exec xs)

def sigma : Letter → List Letter
  | .a => [.a, .b, .a]
  | .b => [.b, .b, .a]

def subst (xs : List Letter) : List Letter := xs.flatMap sigma

def liftScan (s : Scan) : Scan :=
  ⟨s.height, 2*s.finalA, s.finalA+s.finalB⟩

theorem blockA (s : Scan) :
    exec (sigma .a) (liftScan s) = (step .a s).map liftScan := by
  rcases s with ⟨h,fa,fb⟩
  cases h with
  | zero => rfl
  | succ h =>
      cases h with
      | zero =>
          simp [sigma, exec, step, liftScan] <;> omega
      | succ h =>
          simp [sigma, exec, step, liftScan] <;> omega

theorem blockB (s : Scan) :
    exec (sigma .b) (liftScan s) = (step .b s).map liftScan := by
  rcases s with ⟨h,fa,fb⟩
  cases h with
  | zero =>
      simp [sigma, exec, step, liftScan] <;> omega
  | succ h =>
      simp [sigma, exec, step, liftScan] <;> omega

theorem block (x : Letter) (s : Scan) :
    exec (sigma x) (liftScan s) = (step x s).map liftScan := by
  cases x
  · exact blockA s
  · exact blockB s

theorem exec_append (u v : List Letter) (s : Scan) :
    exec (u ++ v) s = (exec u s).bind (exec v) := by
  induction u generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, exec]
      cases h : step x s with
      | none => simp [h]
      | some s' => simp [h, ih]

/-- The finite-state rescaling law for arbitrary words. Every failed
    low scan is a failed high scan as well; every successful low scan
    transports the height and both terminal counts exactly. -/
theorem subst_scan (xs : List Letter) (s : Scan) :
    exec (subst xs) (liftScan s) = (exec xs s).map liftScan := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have happend : subst (x::xs) = sigma x ++ subst xs := rfl
      rw [happend, exec_append, block]
      cases h : step x s with
      | none => simp [exec, h]
      | some s' =>
          simpa [exec, h] using ih s'

def initial : Scan := ⟨1, 0, 0⟩
def W : Nat → List Letter
  | 0 => [.a, .b, .b, .a]
  | n+1 => subst (W n)

theorem base : exec (W 0) initial = some ⟨1,1,1⟩ := by decide

/-- Both final-run event counts double at every substitution:
    #finalA(W_n) = #finalB(W_n) = 2^n, even though |W_n|=4*3^n. -/
theorem final_run_counts (n : Nat) :
    exec (W n) initial = some ⟨1,2^n,2^n⟩ := by
  induction n with
  | zero => exact base
  | succ n ih =>
      change exec (subst (W n)) initial =
        some ⟨1,2^(n+1),2^(n+1)⟩
      have h := subst_scan (W n) initial
      change exec (subst (W n)) initial =
        (exec (W n) initial).map liftScan at h
      rw [h, ih]
      simp [liftScan, Nat.pow_succ]
      omega

#print axioms blockA
#print axioms blockB
#print axioms subst_scan
#print axioms final_run_counts

end BB6.Agent4Raw56LE17557TerminalCounts
