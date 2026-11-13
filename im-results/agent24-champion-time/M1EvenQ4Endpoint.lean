import TM63RootQ4Drain
import M1EvenQ4Prefix
import Q4RightEndpoint
import Lean.Elab.Tactic.Omega

/-!
# Root-connected m=1,n=6 even q4 endpoint

This module consumes Agent 48's finite m=1,n=6 source prefix and Agent
24's branch-independent q4 suffix-to-S1 endpoint.  It proves the complete
canonical S1 endpoint of that reset stage, then composes it with the
already-defined blank-root q4/drain prefix.

The source modules remain proof candidates until the repository's manual
Lean workflow compiles the full dependency closure.
-/

namespace BB6Coverage.Agent24M1EvenEndpoint

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24Q4Endpoint

/-- The m=1,n=6 q4 cut retains the blank exterior beyond the right
unary counter.  This supplies the open-tail premise needed by the generic
q4 suffix endpoint. -/
theorem m1Even_q4_prefix_far_tail (a b : Nat) (h : Int) :
    ∀ i : Nat, 9+3*b ≤ i →
      m1EvenQ4CutTape a b h (h+1+(i:Int)) = false := by
  intro i hi
  let T : Int → Bool := (s1Config 3 6 1 a 0 b h).tape
  let N : Nat := 3*a+1
  let T1 : Int → Bool := sweptLeft N T h
  have hout : m1EvenQ4Inside
      ((h+1+(i:Int))-(h-(N:Int))) = false := by
    simp [m1EvenQ4Inside,N]
    omega
  have hframe :
      m1EvenQ4CutTape a b h (h+1+(i:Int)) =
        T1 (h+1+(i:Int)) := by
    change (frameAt T1 (h-(N:Int))
      m1EvenQ4Inside m1EvenQ4BridgeEnd).tape
        (h+1+(i:Int)) = T1 (h+1+(i:Int))
    rw [frameAt_tape]
    simp [hout]
  have hpres :
      T1 (h+1+(i:Int)) = T (h+1+(i:Int)) := by
    exact sweptLeft_preserves_right N T h (h+1+(i:Int)) (by omega)
  have hsrc :
      T (h+1+(i:Int)) = sideBit (s0RightFacing b) i := by
    simpa [T] using s1Config_right_cell 3 6 1 a 0 b h i
  have hlen : (s0RightFacing b).length = 9+3*b := by
    simp [s0RightFacing,d1pow_length]
    omega
  have hblank : sideBit (s0RightFacing b) i = false := by
    exact BB6Coverage.Agent6Q4Prefix.sideBit_ge_length
      (s0RightFacing b) i (by omega)
  exact hframe.trans (hpres.trans (hsrc.trans hblank))

/-- Complete original-table m=1,n=6 even reset prefix, now ending at
the canonical marker-0 S1 configuration rather than an opaque finite
suffix frame. -/
theorem m1Even_reset_prefix_to_s1 (a b : Nat) (h : Int) :
    run tm2 (resetPrefixCost 1 6 a b)
      ⟨3,h,(s1Config 3 6 1 a 0 b h).tape⟩ =
      some (s1Config 3 5 0 (a+b+2) (2^b-1) 0
        (h+5+(3*b:Int))) := by
  rw [m1Even_reset_prefix_frame_cost a b h]
  have hframe := q4_suffix_frame_eq_s1Config
    (m1EvenQ4CutTape a b h) h b
    3 5 0 (a+b+2) (2^b-1)
    (m1EvenQ4LeftFacing a)
    (m1Even_q4_prefix_rightShape a b h)
    (m1Even_q4_prefix_far_tail a b h)
    (m1Even_q4_prefix_leftFacing a b h)
    (m1EvenQ4SuffixTargetLeft a b)
  exact congrArg some hframe

/-- Exact arithmetic length of the blank-root q4/drain prefix followed
by the m=1,n=6 even reset stage. -/
theorem tm63_root_m1Even_prefix_cost :
    rootQ4DrainMoves + resetPrefixCost 1 6 71 (2^63-1) =
      6*4^63 + 45*2^63 + 28415 := by
  rw [rootQ4DrainMoves_closed, m1Even_resetPrefixCost_eq]
  omega

/-- The blank-root TM63 run continues through the m=1,n=6 even reset
stage to the next canonical S1 state.  This is a source-prefix theorem,
not a halting or Busy Beaver optimality claim. -/
theorem tm2_blank_reaches_m1Even_s1 :
    run tm2 (rootQ4DrainMoves + resetPrefixCost 1 6 71 (2^63-1)) blank =
      some (s1Config 3 5 0 (71+(2^63-1)+2)
        (2^(2^63-1)-1) 0
        (223+5+(3*(2^63-1):Int))) := by
  rw [run_add tm2 blank rootQ4DrainMoves
    (resetPrefixCost 1 6 71 (2^63-1))]
  rw [tm2_blank_reaches_q4_drain_endpoint]
  simpa only [Option.bind_some] using
    m1Even_reset_prefix_to_s1 71 (2^63-1) 223

#print axioms m1Even_q4_prefix_far_tail
#print axioms m1Even_reset_prefix_to_s1
#print axioms tm63_root_m1Even_prefix_cost
#print axioms tm2_blank_reaches_m1Even_s1

end BB6Coverage.Agent24M1EvenEndpoint
