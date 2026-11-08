import MidAposBoundary
import JuncCanonical
import FirstGateRaw
import Lean.Elab.Tactic.Omega

namespace BB429FirstGateMidA
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429High3Ladder
open BB429OddExcursion BB429JuncHeadExcursion BB429PhysicalBridge
open BB429DeltaPhysicalBridge BB429JuncCanonical BB429FirstGateRays
open BB429FirstGateRaw BB429MidAposBoundary

/-- The source-certified Junc representation is the *entire* physical J tape;
    consequently an exact raw halt on a canonical J also holds from every
    physical configuration representing that zipper, at any head coordinate. -/
theorem represented_junc_halts (u w n : Nat) (c : Config)
    (hrep : Represents (junc u 0 w) c)
    (hh : run target429 n (jConfig u w) = none) :
    run target429 n c = none := by
  have hc := represented_junc_eq_translatedJ u w c hrep
  have hJ : translatedJ u w c.head =
      shiftConfig c.head (jConfig u w) := by
    simp [translatedJ, shiftConfig, jConfig]
  calc
    run target429 n c =
        run target429 n (translatedJ u w c.head) := by rw [hc]
    _ = run target429 n (shiftConfig c.head (jConfig u w)) := by rw [hJ]
    _ = none := by rw [run_shiftConfig, hh]; rfl

/-- Every genuine physical configuration representing the zero-u right-five
    MidA input with an even parameter 2*K_even(m) halts under the actual
    six-state table. No blank-root reachability premise is asserted. -/
theorem even_midA_raw_halts (m : Nat) (c : Config)
    (hrep : Represents (midApos 0 (2*(evenK m)) 5) c) :
    run target429
      ((26*(evenK m)+177) +
        (branchCostSum 3 (4*(m+1)) + branchCost (branchU 3 (4*(m+1))))) c = none := by
  let k : Nat := evenK m
  obtain ⟨c', hpre, hrepJ, _⟩ :=
    source_runWithDelta_rep (26*k+177) (midApos 0 (2*k) 5) c hrep
      (junc 3 0 (4*k+17)) (-((4*k+7 : Nat) : Int))
      (midApos_zero_w5_even_to_junc3_delta k)
  have hhalt : run target429
      (branchCostSum 3 (4*(m+1)) + branchCost (branchU 3 (4*(m+1))))
      c' = none :=
    represented_junc_halts 3 (4*k+17) _ c' hrepJ (even_raw_fatal m)
  rw [BB6Bubble.run_add', hpre]
  exact hhalt

/-- Odd-parameter right-five MidA inputs also contain an explicit infinite
    family of complete prepared tapes halting under the original machine. -/
theorem odd_midA_raw_halts (m : Nat) (c : Config)
    (hrep : Represents (midApos 0 (2*(oddK m)+1) 5) c) :
    run target429
      ((26*(oddK m)+354) +
        (branchCostSum 11 (4*m+1) + branchCost (branchU 11 (4*m+1)))) c = none := by
  let k : Nat := oddK m
  obtain ⟨c', hpre, hrepJ, _⟩ :=
    source_runWithDelta_rep (26*k+354) (midApos 0 (2*k+1) 5) c hrep
      (junc 11 0 (4*k+10)) (-((4*k : Nat) : Int))
      (midApos_zero_w5_odd_to_junc11_delta k)
  have hhalt : run target429
      (branchCostSum 11 (4*m+1) + branchCost (branchU 11 (4*m+1)))
      c' = none :=
    represented_junc_halts 11 (4*k+10) _ c' hrepJ (odd_raw_fatal m)
  rw [BB6Bubble.run_add', hpre]
  exact hhalt

#print axioms represented_junc_halts
#print axioms even_midA_raw_halts
#print axioms odd_midA_raw_halts
end BB429FirstGateMidA
