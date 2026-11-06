import Lean.Elab.Tactic.Omega

/-!
  Standalone exact-literal-source verification of the local E marker pump.
  All twelve entries of 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---
  are explicitly encoded, including the absorbing halted state 6.
  Not yet imported against the unchanged original CryptidBoundary module.
-/

namespace BB6.ESeamPump

structure Cfg where
  l : List Bool
  h : Bool
  r : List Bool
  st : Nat
  deriving Repr, DecidableEq

def goL (c : Cfg) (wr : Bool) (st : Nat) : Cfg :=
  match c.l with
  | [] => ⟨[], false, wr :: c.r, st⟩
  | b :: bs => ⟨bs, b, wr :: c.r, st⟩

def goR (c : Cfg) (wr : Bool) (st : Nat) : Cfg :=
  match c.r with
  | [] => ⟨wr :: c.l, false, [], st⟩
  | b :: bs => ⟨wr :: c.l, b, bs, st⟩

def step (c : Cfg) : Cfg :=
  match c.st, c.h with
  | 0, false => goR c true 1
  | 0, true  => goR c false 4
  | 1, false => goL c true 2
  | 1, true  => goR c false 0
  | 2, false => goL c true 0
  | 2, true  => goL c true 3
  | 3, false => goL c true 2
  | 3, true  => goL c true 5
  | 4, false => goL c false 2
  | 4, true  => goL c false 1
  | 5, false => goL c true 4
  | 5, true  => ⟨c.l, c.h, c.r, 6⟩
  | _, _ => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | t+1, c => run t (step c)

theorem run_add (a b : Nat) (c : Cfg) :
    run (a+b) c = run b (run a c) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih => simpa [run, Nat.succ_add] using ih (step c)

def markedStack : Nat → List Bool
  | 0 => [true]
  | m+1 => false :: true :: markedStack m

private theorem two_step (m : Nat) (ys : List Bool) :
    run 2 (⟨markedStack (m+1), true, ys, 2⟩ : Cfg) =
      ⟨markedStack m, true, [true,true] ++ ys, 2⟩ := by
  rfl

/-- Every number of inserted 10 pairs yields 2 extra primitive steps
    and two extra right 1s. Final left list is exactly empty. -/
theorem marker_sweep (m : Nat) (ys : List Bool) :
    run (2*m+2) (⟨markedStack m, true, ys, 2⟩ : Cfg) =
      ⟨[], false, List.replicate (2*m+2) true ++ ys, 5⟩ := by
  induction m generalizing ys with
  | zero => rfl
  | succ m ih =>
    have ht : 2*(m+1)+2 = 2 + (2*m+2) := by omega
    rw [ht, run_add, two_step, ih]
    congr 1
    calc
      List.replicate (2*m+2) true ++ ([true,true] ++ ys) =
          (List.replicate (2*m+2) true ++ List.replicate 2 true) ++ ys := by
            simp only [List.replicate_succ, List.replicate_zero,
              List.cons_append, List.append_assoc]
      _ = List.replicate ((2*m+2)+2) true ++ ys := by
            rw [List.replicate_append_replicate]
      _ = List.replicate (2+(2*m+2)) true ++ ys := by
            rw [show (2*m+2)+2 = 2+(2*m+2) by omega]

#print axioms run_add
#print axioms two_step
#print axioms marker_sweep
end BB6.ESeamPump
