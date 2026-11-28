import Agent22ExactDrainCocycleDepthSource
import Agent49DrainLinearLogSource

/-!
# Joint B-drain outer-depth, first-counter growth and weighted potential

A successful original-source B-drain whose ternary budget is available
has a single *shared* outer-iteration count r such that:
  r <= n, output-first <= input-first+r,
  2*output-first+output-third = 2*input-first+input-third+3*b+2*r.
The second claim is stronger than independently bounding the output-first
by a+n and bounding r by n. It provides a one-sided correction constraint
crucial for signed BB6 #623 terminal strip calculations.
-/

namespace BB6.Agent27DrainWeightedFirstCoupledSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent22ExactDrainCocycleSource
open BB6.Agent22ExactDrainCocycleDepthSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem drainB_weighted_depth_first_upper (n : Nat) :
    ∀ a b d aa dd : Nat, b ≤ ternaryOnes a → b < 3^n →
      drainB a b d = some (.D aa dd) →
      ∃ r : Nat, r≤n ∧ aa≤a+r ∧
        2*aa+dd = 2*a+d+3*b+2*r := by
  induction n with
  | zero =>
      intro a b d aa dd hbudget hpow hs
      have hb0 : b=0 := by omega
      subst b
      rw [drainB] at hs
      simp at hs
      cases hs
      exact ⟨0, by omega, by omega, by omega⟩
  | succ n ih =>
      intro a b d aa dd hbudget hpow hs
      by_cases hb0 : b=0
      · subst b
        rw [drainB] at hs
        simp at hs
        cases hs
        exact ⟨0, by omega, by omega, by omega⟩
      · have hstrict : b-1<ternaryOnes a := by omega
        rw [drainB] at hs
        simp only [if_neg hb0] at hs
        obtain ⟨a1,b1,d1,he,hbudget1⟩ :=
          evalA_ones_budget a (b-1) (d+2*b+3) hstrict
        have hq := evalA_second_le_quotient a (b-1)
          (d+2*b+3) a1 b1 d1 he
        have hdec : b1<b := by omega
        have hpowSub : b-1<3^(n+1) := by omega
        have hdiv : (b-1)/3<3^n := by
          apply (Nat.div_lt_iff_lt_mul (by decide : 0<3)).2
          simpa [Nat.pow_succ,Nat.mul_comm] using hpowSub
        have hpow1 : b1<3^n := by omega
        simp only [he,Option.bind_some,if_pos hdec] at hs
        obtain ⟨r,hr,hfirst,hEq⟩ := ih a1 b1 d1 aa dd hbudget1 hpow1 hs
        have hupper := evalA_first_upper_one a (b-1) (d+2*b+3) a1 b1 d1 he
        have hweighted := evalA_weighted_exact a (b-1)
          (d+2*b+3) a1 b1 d1 hstrict he
        refine ⟨r+1,?_,?_,?_⟩ <;> omega

#print axioms drainB_weighted_depth_first_upper

end BB6.Agent27DrainWeightedFirstCoupledSource
