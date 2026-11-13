import Q4Suffix
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# TM63 q4 suffix: exact right-facing endpoint

The q4 suffix's final local frame determines the nine-cell canonical S0
right word.  Its cells beyond the local frame are unchanged by the
first-ten frame, counted scan, and final tail.  The only extra input
needed for a *full tape* equality is the source prefix's infinite blank
right tail; this module isolates that interface.
-/

namespace BB6Coverage.Agent24Q4Endpoint

open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8S1Encoder

/-- The exact prefix right-stream theorem implies the infinite blank tail
    needed to identify the suffix's entire right half. -/
theorem q4_prefix_far_tail (b : Nat) (Tq : Int → Bool) (h : Int)
    (hright : ∀ i : Nat,
      Tq (h+1+(i:Int)) =
        BB6Coverage.Agent8S1Encoder.sideBit
          (BB6Coverage.Agent6Q4Prefix.q4RightFacing b) i) :
    ∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false := by
  intro i hi
  rw [hright]
  have hlen :=
    BB6Coverage.Agent6Q4Prefix.q4RightFacing_length b
  exact BB6Coverage.Agent8S1Encoder.sideBit_ge_length
    (BB6Coverage.Agent6Q4Prefix.q4RightFacing b) i (by omega)

/-- A cell in the final 29-move local frame, expressed relative to its
    origin g. -/
private theorem q4_tail_frame_cell (T : Int → Bool) (g r : Int)
    (hr : -4 ≤ r ∧ r ≤ 4) :
    (frameAt T g q4TailInside q4TailEnd).tape (g+r) =
      decide (r ∈ q4TailEnd.marked) := by
  rw [frameAt_tape]
  have hcoord : g+r-g = r := by omega
  rw [hcoord]
  have hin : q4TailInside r = true := by
    simp [q4TailInside]
    omega
  simp [hin]

/-- The original q4 suffix frame has exactly the target's nine-cell
    right-facing word, and preserves the blank ray beyond it. -/
theorem q4_suffix_right_word (T : Int → Bool) (h : Int) (b : Nat)
    (hshape : q4RightShape T h b)
    (htail : ∀ i : Nat, 9+3*b ≤ i →
      T (h+1+(i:Int)) = false) :
    ∀ i : Nat,
      (frameAt
        (d0Sweep b
          (frameAt T h q4First10Inside q4First10End).tape
          (h+10))
        (h+10+(3*b:Int)) q4TailInside q4TailEnd).tape
          (h+6+(3*b:Int)+(i:Int)) =
      sideBit (s0RightFacing 0) i := by
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  intro i
  change U.tape (h+6+(3*b:Int)+(i:Int)) =
    sideBit (s0RightFacing 0) i
  by_cases hi : i < 9
  · have hcoord :
        h+6+(3*b:Int)+(i:Int) = g+(-4+(i:Int)) := by
      dsimp [g]
      omega
    rw [hcoord]
    have hrange : -4 ≤ (-4+(i:Int)) ∧ (-4+(i:Int)) ≤ 4 := by omega
    have hv := q4_tail_frame_cell T2 g (-4+(i:Int)) hrange
    have hcases :
        i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
        i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    all_goals
      subst i
      simpa [U, q4TailEnd, s0RightFacing, d1pow, d1, sideBit] using hv
  · have hi9 : 9 ≤ i := by omega
    let x : Int := h+6+(3*b:Int)+(i:Int)
    have hframe : U.tape x = T2 x := by
      dsimp [U]
      rw [frameAt_tape]
      have hnot : q4TailInside (x-g) = false := by
        simp [q4TailInside]
        dsimp [x,g]
        omega
      simp [hnot]
    have hscan : T2 x = T1 x := by
      dsimp [T2]
      exact d0Sweep_after b T1 (h+10) x (by
        dsimp [x,g]
        omega)
    have hfirst : T1 x = T x := by
      dsimp [T1]
      rw [frameAt_tape]
      have hnot : q4First10Inside (x-h) = false := by
        simp [q4First10Inside]
        dsimp [x,g]
        omega
      simp [hnot]
    have hidx : x = h+1+((5+3*b+i:Int)) := by
      dsimp [x,g]
      omega
    have hzero := htail (5+3*b+i) (by omega)
    have hlen : (s0RightFacing 0).length = 9 := by
      simp [s0RightFacing, d1pow, d1]
    have htarget :
        sideBit (s0RightFacing 0) i = false :=
      BB6Coverage.Agent8S1Encoder.sideBit_ge_length
        (s0RightFacing 0) i (by omega)
    calc
      U.tape (h+6+(3*b:Int)+(i:Int)) = U.tape x := by rfl
      _ = T2 x := hframe
      _ = T1 x := hscan
      _ = T x := hfirst
      _ = false := by
        rw [hidx]
        exact hzero
      _ = sideBit (s0RightFacing 0) i := htarget.symm

#print axioms q4_prefix_far_tail
#print axioms q4_suffix_right_word

end BB6Coverage.Agent24Q4Endpoint
