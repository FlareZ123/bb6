import CountedResetBase
import CountedCarryBridges
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent8CountedReset

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder

/-- For an odd positive source counter, BinDec starts with the d0 block.
    The remaining suffix is exactly the same suffix used by n-1. -/
theorem binDec_odd_head (L n : Nat) (hn : n % 2 = 1)
    (hbound : n < 2^L) :
    binDec L n = d0 ++ binDec (L-1) (n/2) := by
  have hL : 0 < L := by
    by_contra hL
    have hL0 : L = 0 := by omega
    subst L
    norm_num at hbound
    omega
  have hlen : L = (L-1)+1 := by omega
  have hnEq : n = 2*(n/2)+1 := by omega
  have hPow : 2^L = 2^(L-1)*2 := by
    rw [hlen, Nat.pow_succ]
  have hq : n/2 < 2^(L-1) := by
    rw [hPow] at hbound
    omega
  rw [hlen, hnEq]
  exact binDec_odd (L-1) (n/2) hq

/-- The source S1 tape agrees with the three marker-specific local reset
    input frames whenever the inner binary counter is odd. The frame only
    sees the marker, d0, the first d0 block of BinDec, and the fixed right
    separator; all later counter bits are arbitrary background. -/
theorem resetBase_source_matches (L n m : Nat) (hm : m < 3)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    ∀ y : Int, resetBaseInside m y = true →
      (embed (resetBaseInput m)).tape y =
        (s1Config L n m 0 0 0 0).tape y := by
  intro y hy
  have hbin := binDec_odd_head L n hn hbound
  interval_cases m
  · have hyb : -7 ≤ y ∧ y ≤ 14 := by
      simpa [resetBaseInside] using hy
    interval_cases y <;>
      norm_num [embed, resetBaseInput, resetBaseInput0,
        s1Config, s0Config, s0Tape, s0LeftFacing, s0RightFacing, s0PhysicalRight,
        markerWord, d0, d1pow, d1, lh, sideBit, binDec_zero, hbin]
  · have hyb : -8 ≤ y ∧ y ≤ 14 := by
      simpa [resetBaseInside] using hy
    interval_cases y <;>
      norm_num [embed, resetBaseInput, resetBaseInput1,
        s1Config, s0Config, s0Tape, s0LeftFacing, s0RightFacing, s0PhysicalRight,
        markerWord, d0, d1pow, d1, lh, sideBit, binDec_zero, hbin]
  · have hyb : -8 ≤ y ∧ y ≤ 14 := by
      simpa [resetBaseInside] using hy
    interval_cases y <;>
      norm_num [embed, resetBaseInput, resetBaseInput2,
        s1Config, s0Config, s0Tape, s0LeftFacing, s0RightFacing, s0PhysicalRight,
        markerWord, d0, d1pow, d1, lh, sideBit, binDec_zero, hbin]

/-- The tape of an S1 configuration is covariant under root translation. -/
theorem s1Config_tape_shift (L n m a z b : Nat) (h x : Int) :
    (s1Config L n m a z b h).tape x =
      (s1Config L n m a z b 0).tape (x-h) := by
  unfold s1Config s0Config s0Tape
  by_cases hx : x ≤ h
  · have hx0 : x-h ≤ 0 := by omega
    have harg : h-x = 0-(x-h) := by omega
    simp [hx, hx0, harg]
  · have hx0 : ¬ x-h ≤ 0 := by omega
    simp [hx, hx0]

/-- Lift the exact finite reset base trace to every S1 source with odd n,
    arbitrary L, and a=b=0. This is a framed intermediate theorem: the
    output frame is source-connected, but the final S0 target equality is
    left as the next embedding obligation. -/
theorem resetBase_odd_frame (L n m : Nat) (h : Int) (hm : m < 3)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    run tm2 (63 + 4*m) (s1Config L n m 0 0 0 h) =
      some (frame (fun x => resetBaseInside m (x-h))
        (s1Config L n m 0 0 0 h).tape
        (shiftConfig h (embed (resetBaseOutput m)))) := by
  have htrace : ∀ bg,
      run tm2 (63 + 4*m)
        (frame (resetBaseInside m) bg (embed (resetBaseInput m))) =
      some (frame (resetBaseInside m) bg (embed (resetBaseOutput m))) :=
    resetBase_frame m hm
  have hmatch : ∀ x, resetBaseInside m (x-h) = true →
      (embed (resetBaseInput m)).tape (x-h) =
        (s1Config L n m 0 0 0 h).tape x := by
    intro x hx
    have hlocal := resetBase_source_matches L n m hm hn hbound (x-h) hx
    rw [s1Config_tape_shift L n m 0 0 0 h x]
    exact hlocal
  have hmain := carryBridgeLift (resetBaseInside m)
    (embed (resetBaseInput m)) (embed (resetBaseOutput m))
    (63 + 4*m) htrace (s1Config L n m 0 0 0 h).tape h hmatch
  have hin :
      {shiftConfig h (embed (resetBaseInput m)) with
        tape := (s1Config L n m 0 0 0 h).tape} =
      s1Config L n m 0 0 0 h := by
    ext <;> simp [shiftConfig, embed, s1Config, s0Config]
  rw [← hin] at hmain
  exact hmain

#print axioms binDec_odd_head
#print axioms resetBase_source_matches
#print axioms resetBase_odd_frame

end BB6Coverage.Agent8CountedReset