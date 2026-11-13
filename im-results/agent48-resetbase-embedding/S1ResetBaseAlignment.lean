import CountedResetBase
import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48ResetBaseEmbedding

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset

/-- Pointwise tape lookup distributes over concatenation. -/
theorem sideBit_append (xs ys : List Bool) (i : Nat) :
    sideBit (xs ++ ys) i =
      if i < xs.length then sideBit xs i else sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons a xs ih =>
      cases i with
      | zero =>
          simp [sideBit]
      | succ i =>
          simp only [List.length_cons, sideBit]
          rw [ih]
          by_cases h : i < xs.length
          · simp [h]
          · have hle : xs.length ≤ i := by omega
            simp [h, hle]
            congr 1
            omega

theorem sideBit_append_lt (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  rw [sideBit_append]
  simp [hi]

theorem sideBit_append_ge (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  rw [sideBit_append]
  simp [not_lt_of_ge hi]

/-- A side stream is blank after its finite support. -/
theorem sideBit_ge_length (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) : sideBit xs i = false := by
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons a xs ih =>
      cases i with
      | zero =>
          simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by
            simp at hi
            omega
          simpa [sideBit] using ih i hi'

/-- The first complemented digit of one is d0, followed by an unchanged
all-one suffix. -/
theorem binDec_one (L : Nat) (hL : 0 < L) :
    binDec L 1 = d0 ++ d1pow (L-1) := by
  have hL' : L = (L-1)+1 := by omega
  rw [hL']
  rw [binDec_odd (L-1) 0 (by simp)]
  rw [binDec_zero]

theorem d1pow_succ_from_pos (L : Nat) (hL : 0 < L) :
    d1pow L = d1 ++ d1pow (L-1) := by
  have hL' : L = (L-1)+1 := by omega
  rw [hL']
  rfl

/-- Before the reset-base trace, the S1 left stream consists of the
marker and separator, one d0 counter digit, then a shared all-one tail. -/
theorem resetBase_input_leftStream (L m : Nat) (hL : 0 < L) :
    s1LeftFacing L 1 m 0 0 =
      (markerWord m ++ d0) ++ (d0 ++ (d1pow (L-1) ++ lh)) := by
  simp [s1LeftFacing, binDec_zero, binDec_one L hL, List.append_assoc]

/-- After the trace and the five-cell head displacement, the S1 left
stream has the same tail, with the first d0 digit replaced by d1. -/
theorem resetBase_output_leftStream (L m : Nat) (hL : 0 < L) :
    s1LeftFacing L 0 ((m+2)%3) (resetDelta m) 0 0 =
      (d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0) ++
        (d1 ++ (d1pow (L-1) ++ lh)) := by
  have hpow := d1pow_succ_from_pos L hL
  simp [s1LeftFacing, binDec_zero, hpow, List.append_assoc]

/-- The reset marker/length update moves the beginning of the shared
counter suffix by exactly the same five cells as the head. -/
theorem resetBase_leftPrefix_length (m : Nat) (hm : m < 3) :
    (d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0).length =
      (markerWord m ++ d0).length + 5 := by
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm' with rfl | rfl | rfl <;>
    simp [resetDelta, markerWord, d1pow, d0]

/-- Once the first three-cell counter digit has been passed, the
head-facing left streams agree after translating the output index by
the five-cell head displacement. -/
theorem sideBit_suffix_shift (p q s : List Bool) (i : Nat)
    (hpq : q.length = p.length + 5)
    (hi : p.length + 3 ≤ i) :
    sideBit (p ++ (d0 ++ s)) i =
      sideBit (q ++ (d1 ++ s)) (i+5) := by
  have hd0 : d0.length = 3 := by decide
  have hd1 : d1.length = 3 := by decide
  rw [sideBit_append_ge p (d0 ++ s) i (by omega)]
  rw [sideBit_append_ge d0 s (i-p.length) (by omega)]
  rw [sideBit_append_ge q (d1 ++ s) (i+5) (by omega)]
  rw [sideBit_append_ge d1 s (i+5-q.length) (by omega)]
  have hidx : (i-p.length)-d0.length =
      (i+5-q.length)-d1.length := by omega
  rw [hidx]

/-- The unbounded left suffix of the input and output S1 encodings is
identical at the same absolute tape cells. -/
theorem resetBase_leftSuffix_agrees (L m : Nat) (hL : 0 < L)
    (hm : m < 3) (i : Nat)
    (hi : (markerWord m ++ d0).length + 3 ≤ i) :
    sideBit (s1LeftFacing L 1 m 0 0) i =
      sideBit (s1LeftFacing L 0 ((m+2)%3) (resetDelta m) 0 0) (i+5) := by
  rw [resetBase_input_leftStream L m hL]
  rw [resetBase_output_leftStream L m hL]
  exact sideBit_suffix_shift
    (markerWord m ++ d0)
    (d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0)
    (d1pow (L-1) ++ lh) i
    (resetBase_leftPrefix_length m hm) hi

/-- For m=2 the finite frame ends one cell before the common suffix:
the third cell of d0 and d1 is already true on both sides. -/
theorem resetBase_leftThirdCell (L : Nat) (hL : 0 < L) :
    sideBit (s1LeftFacing L 1 2 0 0) 9 =
      sideBit (s1LeftFacing L 0 1 2 0 0) 14 := by
  rw [resetBase_input_leftStream L 2 hL]
  rw [resetBase_output_leftStream L 2 hL]
  simp [resetDelta]
  let s := d1pow (L-1) ++ lh
  let p := markerWord 2 ++ d0
  let q := d1pow 2 ++ markerWord 1 ++ d0
  change sideBit (p ++ (d0 ++ s)) 9 =
    sideBit (q ++ (d1 ++ s)) 14
  have hp : p.length = 7 := by simp [p, markerWord, d0]
  have hq : q.length = 12 := by simp [q, markerWord, d1pow, d1, d0]
  calc
    sideBit (p ++ (d0 ++ s)) 9 =
        sideBit (d0 ++ s) (9-p.length) :=
      sideBit_append_ge p (d0 ++ s) 9 (by omega)
    _ = sideBit d0 2 := by
      have hidx : 9-p.length = 2 := by omega
      rw [hidx]
      exact sideBit_append_lt d0 s 2 (by decide)
    _ = true := by decide
    _ = sideBit d1 2 := by decide
    _ = sideBit (d1 ++ s) 2 := by
      symm
      exact sideBit_append_lt d1 s 2 (by decide)
    _ = sideBit (q ++ (d1 ++ s)) 14 := by
      have hidx : 14-q.length = 2 := by omega
      simpa [hidx] using
        (sideBit_append_ge q (d1 ++ s) 14 (by omega)).symm

/-- The two S1 tapes in the n=1, a=b=0 reset base agree everywhere
outside the finite frame touched by the corresponding base trace.  This
is the infinite-context part of the S1 embedding; the finite cells inside
the frame are handled separately. -/
theorem resetBase_s1_outside (L m : Nat) (hL : 0 < L) (hm : m < 3)
    (x : Int) (hout : resetBaseInside m x = false) :
    (s1Config L 1 m 0 0 0 0).tape x =
      (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5).tape x := by
  by_cases hx : x ≤ 0
  · let i : Nat := Int.toNat (-x)
    let j : Nat := Int.toNat (5-x)
    have hiCast : (i : Int) = -x := by
      dsimp [i]
      exact Int.toNat_of_nonneg (by omega)
    have hjCast : (j : Int) = 5-x := by
      dsimp [j]
      exact Int.toNat_of_nonneg (by omega)
    have hcoordIn : (0:Int) - (i:Int) = x := by
      rw [hiCast]
      omega
    have hcoordOut : (5:Int) - (j:Int) = x := by
      rw [hjCast]
      omega
    have hindex : j = i+5 := by omega
    have hside :
        sideBit (s1LeftFacing L 1 m 0 0) i =
          sideBit (s1LeftFacing L 0 ((m+2)%3) (resetDelta m) 0 0) (i+5) := by
      have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm' with rfl | rfl | rfl
      · have hnot : ¬ (-7 ≤ x ∧ x ≤ 14) := by
          simpa [resetBaseInside] using hout
        have hxlo : x < -7 := by omega
        have hi8 : 8 ≤ i := by omega
        have hp : (markerWord 0 ++ d0).length = 5 := by decide
        exact resetBase_leftSuffix_agrees L 0 hL (by omega) i (by rw [hp]; omega)
      · have hnot : ¬ (-8 ≤ x ∧ x ≤ 14) := by
          simpa [resetBaseInside] using hout
        have hxlo : x < -8 := by omega
        have hi9 : 9 ≤ i := by omega
        have hp : (markerWord 1 ++ d0).length = 6 := by decide
        exact resetBase_leftSuffix_agrees L 1 hL (by omega) i (by rw [hp]; omega)
      · have hnot : ¬ (-8 ≤ x ∧ x ≤ 14) := by
          simpa [resetBaseInside] using hout
        have hxlo : x < -8 := by omega
        have hi9 : 9 ≤ i := by omega
        by_cases hiEq : i = 9
        · rw [hiEq]
          exact resetBase_leftThirdCell L hL
        · have hi10 : 10 ≤ i := by omega
          have hp : (markerWord 2 ++ d0).length = 7 := by decide
          exact resetBase_leftSuffix_agrees L 2 hL (by omega) i (by rw [hp]; omega)
    calc
      (s1Config L 1 m 0 0 0 0).tape x =
          (s1Config L 1 m 0 0 0 0).tape (0-(i:Int)) := by rw [hcoordIn]
      _ = sideBit (s1LeftFacing L 1 m 0 0) i :=
        s1Config_left_cell L 1 m 0 0 0 0 i
      _ = sideBit (s1LeftFacing L 0 ((m+2)%3) (resetDelta m) 0 0) (i+5) :=
        hside
      _ = sideBit (s1LeftFacing L 0 ((m+2)%3) (resetDelta m) 0 0) j := by
        rw [hindex]
      _ = (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5).tape (5-(j:Int)) :=
        (s1Config_left_cell L 0 ((m+2)%3) (resetDelta m) 0 0 5 j).symm
      _ = (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5).tape x := by
        rw [hcoordOut]
  · have hx14 : 14 < x := by
      have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm' with rfl | rfl | rfl
      · have hnot : ¬ (-7 ≤ x ∧ x ≤ 14) := by
          simpa [resetBaseInside] using hout
        omega
      · have hnot : ¬ (-8 ≤ x ∧ x ≤ 14) := by
          simpa [resetBaseInside] using hout
        omega
      · have hnot : ¬ (-8 ≤ x ∧ x ≤ 14) := by
          simpa [resetBaseInside] using hout
        omega
    let i : Nat := Int.toNat (x-1)
    let j : Nat := Int.toNat (x-6)
    have hiCast : (i : Int) = x-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg (by omega)
    have hjCast : (j : Int) = x-6 := by
      dsimp [j]
      exact Int.toNat_of_nonneg (by omega)
    have hcoordIn : (0:Int)+1+(i:Int) = x := by
      rw [hiCast]
      omega
    have hcoordOut : (5:Int)+1+(j:Int) = x := by
      rw [hjCast]
      omega
    have hlen : (s1PhysicalRight 0).length = 9 := by
      simp [s1PhysicalRight, s0PhysicalRight, s0RightFacing, d1pow, d1]
    have hiLen : (s1PhysicalRight 0).length ≤ i := by
      rw [hlen]
      omega
    have hjLen : (s1PhysicalRight 0).length ≤ j := by
      rw [hlen]
      omega
    calc
      (s1Config L 1 m 0 0 0 0).tape x =
          (s1Config L 1 m 0 0 0 0).tape (0+1+(i:Int)) := by rw [hcoordIn]
      _ = sideBit (s1PhysicalRight 0) i :=
        s1Config_right_cell L 1 m 0 0 0 0 i
      _ = false := sideBit_ge_length _ _ hiLen
      _ = sideBit (s1PhysicalRight 0) j :=
        (sideBit_ge_length _ _ hjLen).symm
      _ = (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5).tape
          (5+1+(j:Int)) :=
        (s1Config_right_cell L 0 ((m+2)%3) (resetDelta m) 0 0 5 j).symm
      _ = (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5).tape x := by
        rw [hcoordOut]

end BB6Coverage.Agent48ResetBaseEmbedding
