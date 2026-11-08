import Lean
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace BB6.Agent43TwoRun

def smallBad0 (n s r : Nat) : Bool :=
  let q := 8^s
  let P := 2^n
  let D := 14*n+92
  decide (P%q=0 ∧ D%q=0 ∧
    (588*q-98)*(P/q) =
      (224*n+672*s+672*r+800)*8^r +
        (84*n+252*s+272-D/q))

def smallBad1 (n s r : Nat) : Bool :=
  let q := 8^s
  let P := 2^n
  let D := 14*n+92
  decide (P%q=0 ∧ D%q=0 ∧
    (392*q-98)*(P/q) =
      (448*n+1344*s+1344*r+2048)*8^r +
        (56*n+168*s+200-D/q))

/-- Complete kernel-computed scan of the bounded three parameters. -/
theorem no_small_bad0 :
    ∀ n : Fin 14, ∀ s : Fin 3, ∀ r : Fin 13,
      smallBad0 (n.val+14) s.val r.val = false := by decide

theorem no_small_bad1 :
    ∀ n : Fin 14, ∀ s : Fin 3, ∀ r : Fin 13,
      smallBad1 (n.val+14) s.val r.val = false := by decide

#print axioms BB6.Agent43TwoRun.no_small_bad0
#print axioms BB6.Agent43TwoRun.no_small_bad1
end BB6.Agent43TwoRun