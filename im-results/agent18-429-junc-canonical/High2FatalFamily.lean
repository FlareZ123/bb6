import JChartThree
import High3Ladder
import Lean.Elab.Tactic.Omega

namespace BB429High2FatalFamily

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429High3Ladder BB429JChartThree

/-- Number of certified high-3 outer J returns following the high-two
    boundary; every fourth length makes the fatal 2u-1 endpoint integral. -/
def turns (k : Nat) : Nat := 4*k+3

/-- An explicit unbounded family of prepared high-two J configurations. -/
def seed (k : Nat) : Nat := 3*2^(turns k)-(10+3*k)

theorem seed_bound (k : Nat) : 10+3*k ≤ 3*2^(turns k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 2^(turns (k+1)) = 16*2^(turns k) := by
      calc
        2^(turns (k+1)) = 2^(turns k+4) := by congr 1
        _ = 2^(turns k)*2^4 := by rw [Nat.pow_add]
        _ = 16*2^(turns k) := by omega
    rw [hp]
    omega

/-- Distinct indices give strictly increasing initial J parameters. -/
theorem seed_strict (k : Nat) : seed k < seed (k+1) := by
  have h0 := seed_bound k
  have h1 := seed_bound (k+1)
  have hp : 2^(turns (k+1)) = 16*2^(turns k) := by
    calc
      2^(turns (k+1)) = 2^(turns k+4) := by congr 1
      _ = 2^(turns k)*2^4 := by rw [Nat.pow_add]
      _ = 16*2^(turns k) := by omega
  unfold seed
  rw [hp]
  omega

theorem seed_linear (k : Nat) :
    4*seed k + (31+3*(turns k)) = 12*2^(turns k) := by
  have h := seed_bound k
  dsimp [seed,turns] at *
  omega

/-- The high-3 ladder decrement leaves exactly the fatal J boundary. -/
theorem branch_tail (k : Nat) :
    branchShift 0 (turns k) + (2*branchU 0 (turns k)-1) =
      4*seed k + 18 := by
  have h := seed_linear k
  have hU := branchU_closed 0 (turns k)
  have hS := branchShift_closed 0 (turns k)
  have hp : 1 ≤ 2^(turns k) := Nat.one_le_pow (turns k) 2 (by decide)
  omega

theorem branch_fits (k : Nat) :
    branchShift 0 (turns k) ≤ 4*seed k+18 := by
  have hb := branch_tail k
  omega

theorem branch_fatal (k : Nat) :
    (4*seed k+18 - branchShift 0 (turns k)) + 1 =
      2*branchU 0 (turns k) := by
  have ht := branch_tail k
  have hu := branchU_closed 0 (turns k)
  have hp : 2 ≤ 2^(turns k) := by
    rw [show turns k = (4*k+2)+1 by dsimp [turns], Nat.pow_succ]
    have h := Nat.one_le_pow (4*k+2) 2 (by decide)
    omega
  omega

/-- Exact primitive-step bound for the source-certified halting family. -/
def fatalTime (k : Nat) : Nat :=
  (4*seed k*seed k+44*seed k+204) +
    branchCostSum 0 (turns k) +
    branchCost (branchU 0 (turns k))

/-- For every k, the *original* raw six-state machine halts after the
    certified high-two return, 4k+3 consecutive high-3 branches, and the
    fatal C/01 J endpoint. Every initial J tape is synthetic/prepared. -/
theorem high2_fatal_family (k : Nat) :
    run target429 (fatalTime k)
      (jConfig (seed k) (2*seed k+2)) = none := by
  let u : Nat := seed k
  let m : Nat := turns k
  let U : Nat := branchU 0 m
  let w : Nat := 4*u+18 - branchShift 0 m
  let d : Int := (-((2*u+10:Nat):Int)) + (branchShift 0 m : Int)
  let initial : Nat := 4*u*u+44*u+204
  let middle : Nat := branchCostSum 0 m
  let final : Nat := branchCost U
  have hfits : branchShift 0 m ≤ 4*u+18 := branch_fits k
  have hfatal : w+1=2*U := branch_fatal k
  have hfirst :
      run target429 initial (jConfig u (2*u+2)) =
        some (shiftConfig (-((2*u+10:Nat):Int)) (jConfig 0 (4*u+18))) := by
    simpa [initial,u] using j_high2_chart (seed k)
  have hmiddle :
      run target429 middle
        (shiftConfig (-((2*u+10:Nat):Int)) (jConfig 0 (4*u+18))) =
        some (shiftConfig d (jConfig U w)) := by
    simpa [middle,u,m,U,w,d] using
      (j_high3_ladder 0 (4*seed k+18) (turns k)
         (-((2*seed k+10:Nat):Int)) (branch_fits k))
  have hfinal :
      run target429 final (shiftConfig d (jConfig U w)) = none := by
    have hraw : run target429 final (jConfig U w) = none := by
      simpa [final,branchCost,jConfig] using
        (BB429JFirstBranch.j_fatal_branch U w hfatal)
    rw [run_shiftConfig, hraw]
    rfl
  have htwo :
      run target429 (initial+middle) (jConfig u (2*u+2)) =
        some (shiftConfig d (jConfig U w)) := by
    rw [BB6Bubble.run_add' target429 initial middle, hfirst]
    simp only [Option.bind_some]
    exact hmiddle
  change run target429 ((initial+middle)+final)
      (jConfig u (2*u+2)) = none
  rw [BB6Bubble.run_add' target429 (initial+middle) final, htwo]
  simp only [Option.bind_some]
  exact hfinal

#print axioms seed_bound
#print axioms seed_strict
#print axioms branch_fatal
#print axioms high2_fatal_family

end BB429High2FatalFamily
