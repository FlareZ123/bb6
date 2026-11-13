import CountedResetOddBase
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48CountedInc0

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24ChampionTime

/-- The odd reset base changes the low block of BinDec from d0 to d1. -/
theorem resetBase_odd_binDec_even (L n : Nat)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    binDec L (n-1) = d1 ++ binDec (L-1) (n/2) := by
  have hL : 0 < L := by
    by_contra hL
    have hL0 : L = 0 := by omega
    subst L
    norm_num at hbound
    omega
  have hlen : L = (L-1)+1 := by omega
  have hpow : 2^L = 2^(L-1)*2 := by
    rw [hlen, Nat.pow_succ]
  have hnEq : n = 2*(n/2)+1 := by omega
  have hq : n/2 < 2^(L-1) := by
    rw [hpow] at hbound
    omega
  have hsub : n-1 = 2*(n/2) := by omega
  rw [hlen, hsub]
  exact binDec_even (L-1) (n/2) hq

private theorem sideBit_append_after (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons a xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

private theorem sideBit_false_after_length (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) : sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons a xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

/-- Outside the finite reset frame, the old and new left streams agree
after the five-cell head displacement. The m=2 boundary cell is the
third bit of d0/d1, which is one on both sides. -/
private theorem resetBase_odd_left_tail_alignment
    (m : Nat) (hm : m < 3) (B : List Bool) (i : Nat)
    (hi : (if m = 0 then 8 else 9) ≤ i) :
    sideBit (markerWord m ++ d0 ++ d0 ++ B ++ lh) i =
      sideBit
        (d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++
          d0 ++ d1 ++ B ++ lh) (i+5) := by
  interval_cases m
  · have hi8 : 8 ≤ i := by simpa using hi
    have hsrc :
        markerWord 0 ++ d0 ++ d0 ++ B ++ lh =
          (markerWord 0 ++ d0 ++ d0) ++ (B ++ lh) := by
      simp [List.append_assoc]
    have htgt :
        d1pow (resetDelta 0) ++ markerWord ((0+2)%3) ++
            d0 ++ d1 ++ B ++ lh =
          (d1pow 1 ++ markerWord 2 ++ d0 ++ d1) ++ (B ++ lh) := by
      simp [resetDelta, List.append_assoc]
    rw [hsrc, htgt]
    have hslen : (markerWord 0 ++ d0 ++ d0).length = 8 := by decide
    have htlen : (d1pow 1 ++ markerWord 2 ++ d0 ++ d1).length = 13 := by decide
    have hs := sideBit_append_after
      (markerWord 0 ++ d0 ++ d0) (B ++ lh) i (by omega)
    have ht := sideBit_append_after
      (d1pow 1 ++ markerWord 2 ++ d0 ++ d1) (B ++ lh) (i+5) (by omega)
    have hs' :
        sideBit ((markerWord 0 ++ d0 ++ d0) ++ (B ++ lh)) i =
          sideBit (B ++ lh) (i-8) := by
      simpa [hslen] using hs
    have ht' :
        sideBit ((d1pow 1 ++ markerWord 2 ++ d0 ++ d1) ++ (B ++ lh))
            (i+5) =
          sideBit (B ++ lh) ((i+5)-13) := by
      simpa [htlen] using ht
    rw [hs', ht']
    have hidx : i-8 = (i+5)-13 := by omega
    rw [hidx]
  · have hi9 : 9 ≤ i := by simpa using hi
    have hsrc :
        markerWord 1 ++ d0 ++ d0 ++ B ++ lh =
          (markerWord 1 ++ d0 ++ d0) ++ (B ++ lh) := by
      simp [List.append_assoc]
    have htgt :
        d1pow (resetDelta 1) ++ markerWord ((1+2)%3) ++
            d0 ++ d1 ++ B ++ lh =
          (d1pow 2 ++ markerWord 0 ++ d0 ++ d1) ++ (B ++ lh) := by
      simp [resetDelta, List.append_assoc]
    rw [hsrc, htgt]
    have hslen : (markerWord 1 ++ d0 ++ d0).length = 9 := by decide
    have htlen : (d1pow 2 ++ markerWord 0 ++ d0 ++ d1).length = 14 := by decide
    have hs := sideBit_append_after
      (markerWord 1 ++ d0 ++ d0) (B ++ lh) i (by omega)
    have ht := sideBit_append_after
      (d1pow 2 ++ markerWord 0 ++ d0 ++ d1) (B ++ lh) (i+5) (by omega)
    have hs' :
        sideBit ((markerWord 1 ++ d0 ++ d0) ++ (B ++ lh)) i =
          sideBit (B ++ lh) (i-9) := by
      simpa [hslen] using hs
    have ht' :
        sideBit ((d1pow 2 ++ markerWord 0 ++ d0 ++ d1) ++ (B ++ lh))
            (i+5) =
          sideBit (B ++ lh) ((i+5)-14) := by
      simpa [htlen] using ht
    rw [hs', ht']
    have hidx : i-9 = (i+5)-14 := by omega
    rw [hidx]
  · by_cases hi9 : i = 9
    · subst i
      norm_num [markerWord, d0, d1, d1pow, resetDelta, sideBit]
    · have hi10 : 10 ≤ i := by omega
      have hsrc :
          markerWord 2 ++ d0 ++ d0 ++ B ++ lh =
            (markerWord 2 ++ d0 ++ d0) ++ (B ++ lh) := by
        simp [List.append_assoc]
      have htgt :
          d1pow (resetDelta 2) ++ markerWord ((2+2)%3) ++
              d0 ++ d1 ++ B ++ lh =
            (d1pow 2 ++ markerWord 1 ++ d0 ++ d1) ++ (B ++ lh) := by
        simp [resetDelta, List.append_assoc]
      rw [hsrc, htgt]
      have hslen : (markerWord 2 ++ d0 ++ d0).length = 10 := by decide
      have htlen : (d1pow 2 ++ markerWord 1 ++ d0 ++ d1).length = 15 := by decide
      have hs := sideBit_append_after
        (markerWord 2 ++ d0 ++ d0) (B ++ lh) i (by omega)
      have ht := sideBit_append_after
        (d1pow 2 ++ markerWord 1 ++ d0 ++ d1) (B ++ lh) (i+5) (by omega)
      have hs' :
          sideBit ((markerWord 2 ++ d0 ++ d0) ++ (B ++ lh)) i =
            sideBit (B ++ lh) (i-10) := by
        simpa [hslen] using hs
      have ht' :
          sideBit ((d1pow 2 ++ markerWord 1 ++ d0 ++ d1) ++ (B ++ lh))
              (i+5) =
            sideBit (B ++ lh) ((i+5)-15) := by
        simpa [htlen] using ht
      rw [hs', ht']
      have hidx : i-10 = (i+5)-15 := by omega
      rw [hidx]

/-- On the right, both reset-base configurations have the same nine-cell
right stream, followed by blanks. -/
private theorem sideBit_s0Right_zero_false (i : Nat) (hi : 9 ≤ i) :
    sideBit (s0RightFacing 0) i = false := by
  have hlen : (s0RightFacing 0).length = 9 := by
    simp [s0RightFacing, d1pow, d1]
  exact sideBit_false_after_length (s0RightFacing 0) i (by omega)

/-- The finite reset output frame already agrees with the canonical S1
target throughout the complete touched interval. -/
theorem resetBase_odd_local_output
    (L n m : Nat) (hm : m < 3) (hn : n % 2 = 1)
    (hbound : n < 2^L) (y : Int)
    (hy : resetBaseInside m y = true) :
    (embed (resetBaseOutput m)).tape y =
      (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 0).tape (y-5) := by
  have hbinEven := resetBase_odd_binDec_even L n hn hbound
  change (embed (resetBaseOutput m)).tape y =
    s0Tape (markerWord ((m+2)%3) ++ d0 ++ binDec L (n-1) ++ lh)
      (resetDelta m) 0 0 0 (y-5)
  rw [hbinEven]
  interval_cases m
  · have hyb : -7 ≤ y ∧ y ≤ 14 := by
      simpa [resetBaseInside] using hy
    rcases hyb with ⟨hlo,hhi⟩
    interval_cases y <;>
      norm_num [embed, resetBaseOutput, resetBaseOutput0,
        resetBaseOutput1, resetBaseOutput2, s0Tape, s0LeftFacing,
        s0RightFacing, markerWord, d0, d1, d1pow, lh, sideBit,
        binDec_zero]
  · have hyb : -8 ≤ y ∧ y ≤ 14 := by
      simpa [resetBaseInside] using hy
    rcases hyb with ⟨hlo,hhi⟩
    interval_cases y <;>
      norm_num [embed, resetBaseOutput, resetBaseOutput0,
        resetBaseOutput1, resetBaseOutput2, s0Tape, s0LeftFacing,
        s0RightFacing, markerWord, d0, d1, d1pow, lh, sideBit,
        binDec_zero]
  · have hyb : -8 ≤ y ∧ y ≤ 14 := by
      simpa [resetBaseInside] using hy
    rcases hyb with ⟨hlo,hhi⟩
    interval_cases y <;>
      norm_num [embed, resetBaseOutput, resetBaseOutput0,
        resetBaseOutput1, resetBaseOutput2, s0Tape, s0LeftFacing,
        s0RightFacing, markerWord, d0, d1, d1pow, lh, sideBit,
        binDec_zero]

/-- Outside the local frame, the old and new S1 encodings are identical
after accounting for the five-cell head shift. -/
theorem resetBase_odd_input_outside
    (L n m : Nat) (hm : m < 3) (hn : n % 2 = 1)
    (hbound : n < 2^L) (y : Int)
    (hout : resetBaseInside m y ≠ true) :
    (s1Config L n m 0 0 0 0).tape y =
      (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 0).tape (y-5) := by
  have hbinOdd := binDec_odd_head L n hn hbound
  have hbinEven := resetBase_odd_binDec_even L n hn hbound
  let B : List Bool := binDec (L-1) (n/2)
  have hsrcList :
      s0LeftFacing (markerWord m ++ d0 ++ binDec L n ++ lh) 0 0 =
        markerWord m ++ d0 ++ d0 ++ B ++ lh := by
    simp [s0LeftFacing, binDec_zero, hbinOdd, B, List.append_assoc]
  have htgtList :
      s0LeftFacing (markerWord ((m+2)%3) ++ d0 ++
          binDec L (n-1) ++ lh) (resetDelta m) 0 =
        d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++
          d0 ++ d1 ++ B ++ lh := by
    simp [s0LeftFacing, binDec_zero, hbinEven, B, List.append_assoc]
  change s0Tape (markerWord m ++ d0 ++ binDec L n ++ lh) 0 0 0 y =
    s0Tape (markerWord ((m+2)%3) ++ d0 ++ binDec L (n-1) ++ lh)
      (resetDelta m) 0 0 0 (y-5)
  by_cases hy : y ≤ 0
  · let i : Nat := Int.toNat (-y)
    have hnonneg : 0 ≤ -y := by omega
    have hcast : (i : Int) = -y := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hi : (if m = 0 then 8 else 9) ≤ i := by
      by_cases hm0 : m = 0
      · subst m
        have hnot : ¬ (-7 ≤ y ∧ y ≤ 14) := by
          simpa [resetBaseInside] using hout
        have hylt : y < -7 := by
          by_contra hge
          have hlow : -7 ≤ y := by omega
          exact hnot ⟨hlow, by omega⟩
        have hi8 : 8 ≤ i := by omega
        simpa using hi8
      · have hnot : ¬ (-8 ≤ y ∧ y ≤ 14) := by
          have hcases : m = 1 ∨ m = 2 := by omega
          rcases hcases with h1 | h2
          · subst m
            simpa [resetBaseInside] using hout
          · subst m
            simpa [resetBaseInside] using hout
        have hylt : y < -8 := by
          by_contra hge
          have hlow : -8 ≤ y := by omega
          exact hnot ⟨hlow, by omega⟩
        have hi9 : 9 ≤ i := by omega
        simpa [hm0] using hi9
    have hsrcIdx : Int.toNat (0-y) = i := by
      dsimp [i]
      simp
    have htargetCast :
        ((Int.toNat (0-(y-5)) : Nat) : Int) = 0-(y-5) :=
      Int.toNat_of_nonneg (by omega)
    have htargetInt :
        ((Int.toNat (0-(y-5)) : Nat) : Int) = (i+5 : Int) := by
      rw [htargetCast, hcast]
      omega
    have htargetIdx : Int.toNat (0-(y-5)) = i+5 := by omega
    simp only [s0Tape, if_pos hy, if_pos (by omega : y-5 ≤ 0)]
    rw [hsrcList, htgtList, hsrcIdx, htargetIdx]
    exact resetBase_odd_left_tail_alignment m hm B i hi
  · have hgt14 : 14 < y := by
      by_contra hnot14
      have hle14 : y ≤ 14 := by omega
      have hinside : resetBaseInside m y = true := by
        interval_cases m <;> simp [resetBaseInside] <;> omega
      exact hout hinside
    have hsrcNonneg : 0 ≤ y-1 := by omega
    have hsrcCast : ((Int.toNat (y-1) : Nat) : Int) = y-1 :=
      Int.toNat_of_nonneg hsrcNonneg
    have hsrcIdx : 9 ≤ Int.toNat (y-1) := by omega
    have htargetNonneg : 0 ≤ y-6 := by omega
    have htargetCast : ((Int.toNat (y-6) : Nat) : Int) = y-6 :=
      Int.toNat_of_nonneg htargetNonneg
    have htargetIdx : 9 ≤ Int.toNat (y-6) := by omega
    simp only [s0Tape, if_neg hy, if_neg (by omega : ¬ y-5 ≤ 0)]
    have hcoord : y-5-1 = y-6 := by omega
    rw [hcoord]
    rw [sideBit_s0Right_zero_false (Int.toNat (y-1)) hsrcIdx]
    rw [sideBit_s0Right_zero_false (Int.toNat (y-6)) htargetIdx]

private theorem config_ext {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp_all

/-- Exact source-level odd-inner-counter reset prefix in the a=b=0 base
case. The output is the canonical S1 encoding, not merely a framed tape. -/
theorem resetBase_odd_canonical
    (L n m : Nat) (h : Int) (hm : m < 3)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    run tm2 (resetPrefixCost m n 0 0)
      (s1Config L n m 0 0 0 h) =
      some (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 (h+5)) := by
  have hrun := resetBase_odd_frame L n m h hm hn hbound
  have hv : v2 n = 0 := by
    exact v2_of_odd n (by omega)
  have hcost : 63+4*m = resetPrefixCost m n 0 0 := by
    simp [resetPrefixCost, hv]
  rw [hcost] at hrun
  have hcfg :
      frame (resetBaseInside m) (s1Config L n m 0 0 0 h).tape
        (shiftConfig h (embed (resetBaseOutput m))) =
      s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 (h+5) := by
    apply config_ext
    · rfl
    · simp [frame, shiftConfig, embed, resetBaseOutput,
        resetBaseOutput0, resetBaseOutput1, resetBaseOutput2] <;> omega
    · funext x
      let y : Int := x-h
      have hxy : x = h+y := by
        dsimp [y]
        omega
      rw [hxy]
      by_cases hin : resetBaseInside m y = true
      · have hlocal := resetBase_odd_local_output
          L n m hm hn hbound y hin
        have hshift :
            (shiftConfig h (embed (resetBaseOutput m))).tape (h+y) =
              (embed (resetBaseOutput m)).tape y := by
          simp [shiftConfig]
        have htarget :
            (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0
              (h+5)).tape (h+y) =
              (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 0).tape
                (y-5) := by
          have ht := s1Config_tape_shift L (n-1) ((m+2)%3)
            (resetDelta m) 0 0 (h+5) (h+y)
          have hcoord : h+y-(h+5) = y-5 := by omega
          simpa [hcoord] using ht
        simp [frame, hin, hshift, htarget, hlocal]
      · have houtside := resetBase_odd_input_outside
          L n m hm hn hbound y hin
        have hsource :
            (s1Config L n m 0 0 0 h).tape (h+y) =
              (s1Config L n m 0 0 0 0).tape y := by
          have hs := s1Config_tape_shift L n m 0 0 0 h (h+y)
          have hcoord : h+y-h = y := by omega
          simpa [hcoord] using hs
        have htarget :
            (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0
              (h+5)).tape (h+y) =
              (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 0).tape
                (y-5) := by
          have ht := s1Config_tape_shift L (n-1) ((m+2)%3)
            (resetDelta m) 0 0 (h+5) (h+y)
          have hcoord : h+y-(h+5) = y-5 := by omega
          simpa [hcoord] using ht
        simp [frame, hin, hsource, htarget, houtside]
  rw [hcfg] at hrun
  exact hrun

#print axioms resetBase_odd_binDec_even
#print axioms resetBase_odd_local_output
#print axioms resetBase_odd_input_outside
#print axioms resetBase_odd_canonical

end BB6Coverage.Agent48CountedInc0
