import M1EvenResidueSix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M1ZeroOddQ4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48CountedInc0
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- The fixed source-side tail after sweeping the first 3a+1 cells
    of S1(4,8,1,a,0,b). -/
def m1ZeroOddSourceLeftSuffix : List Bool :=
  [false, true] ++ d0 ++ d1 ++ d1 ++ d1 ++ d0 ++ lh

/-- The finite bridge reads only this interval relative to its initial head. -/
def m1ZeroOddBridgeInside (x : Int) : Bool :=
  decide (-15 ≤ x ∧ x ≤ 2)

def m1ZeroOddBridgeStart : FConfig :=
  ⟨3, 0, [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -1, 2]⟩

def m1ZeroOddBridgeEnd : FConfig :=
  ⟨4, 2, [-15, -14, -13, -10, -7, -4, -1, 1, 2]⟩

/-- Exact 62-step finite bridge discovered from the source machine. -/
theorem m1ZeroOddBridge_exact :
    fRun tm2 62 m1ZeroOddBridgeStart = some m1ZeroOddBridgeEnd := by
  decide

/-- Every head read during the finite bridge remains in its framed window. -/
theorem m1ZeroOddBridge_heads :
    (List.range 62).all (fun j =>
      m1ZeroOddBridgeInside
        ((fRun tm2 j m1ZeroOddBridgeStart).getD m1ZeroOddBridgeStart).head) = true := by
  decide

private theorem binDec_three_four :
    binDec 3 4 = d1 ++ d1 ++ d0 := by
  norm_num [binDec, binaryCounterFuel, d0, d1]

private theorem binDec_four_eight :
    binDec 4 8 = d1 ++ d1 ++ d1 ++ d0 := by
  rw [binDec_even 3 4 (by decide)]
  rw [binDec_three_four]

private theorem binDec_three_three :
    binDec 3 3 = d0 ++ d0 ++ d1 := by
  norm_num [binDec, binaryCounterFuel, d0, d1]

private theorem binDec_four_seven :
    binDec 4 7 = d0 ++ d0 ++ d0 ++ d1 := by
  rw [binDec_odd 3 3 (by decide)]
  rw [binDec_three_three]


/-- The q4 cut for the marker-1, n=8 row carries the *marker-0* word:
the following q4 suffix is the source transition to marker 0. -/
def m1ZeroOddQ4LeftFacing (L n a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L n ++ lh

/-- Low four blocks of the marker-1 n=8k source when k is odd. -/
theorem m1ZeroOdd_binDec_residue8 (L k : Nat)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1) (hbound : 8*k < 2^L) :
    binDec L (8*k) =
      d1 ++ d1 ++ d1 ++ d0 ++ binDec (L-4) (k/2) := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow4 : 2^(L-3) = 2 * 2^(L-4) := by
    rw [show L-3 = (L-4)+1 by omega, Nat.pow_succ]
    norm_num
    ring
  have hk : k < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*k < 2^(L-1) := by rw [hpow2]; omega
  have hq2 : 2*k < 2^(L-2) := by rw [hpow1]; omega
  have hk2 : k/2 < 2^(L-4) := by
    rw [hpow4] at hk
    omega
  have hdiv : k = 2*(k/2)+1 := by omega
  have h1 : binDec L (8*k) =
      d1 ++ binDec (L-1) (4*k) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k = 2*(4*k) by omega]
    exact binDec_even (L-1) (4*k) hq1
  have h2 : binDec (L-1) (4*k) =
      d1 ++ binDec (L-2) (2*k) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k = 2*(2*k) by omega]
    exact binDec_even (L-2) (2*k) hq2
  have h3 : binDec (L-2) (2*k) =
      d1 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega,
      show 2*k = 2*k by rfl]
    exact binDec_even (L-3) k hk
  have h4 : binDec (L-3) k =
      d0 ++ binDec (L-4) (k/2) := by
    rw [show L-3 = (L-4)+1 by omega, hdiv]
    exact binDec_odd (L-4) (k/2) hk2
  rw [h1,h2,h3,h4]
  simp [List.append_assoc]

/-- The decremented n=8k-1 word shares the same high-order quotient tail. -/
theorem m1ZeroOdd_binDec_residue7 (L k : Nat)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1) (hbound : 8*k < 2^L) :
    binDec L (8*k-1) =
      d0 ++ d0 ++ d0 ++ d1 ++ binDec (L-4) (k/2) := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow4 : 2^(L-3) = 2 * 2^(L-4) := by
    rw [show L-3 = (L-4)+1 by omega, Nat.pow_succ]
    norm_num
    ring
  have hk : k < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*k-1 < 2^(L-1) := by rw [hpow2]; omega
  have hq2 : 2*k-1 < 2^(L-2) := by rw [hpow1]; omega
  have hk2 : k/2 < 2^(L-4) := by
    rw [hpow4] at hk
    omega
  have hdiv : k-1 = 2*(k/2) := by omega
  have h1 : binDec L (8*k-1) =
      d0 ++ binDec (L-1) (4*k-1) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k-1 = 2*(4*k-1)+1 by omega]
    exact binDec_odd (L-1) (4*k-1) hq1
  have h2 : binDec (L-1) (4*k-1) =
      d0 ++ binDec (L-2) (2*k-1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k-1 = 2*(2*k-1)+1 by omega]
    exact binDec_odd (L-2) (2*k-1) hq2
  have h3 : binDec (L-2) (2*k-1) =
      d0 ++ binDec (L-3) (k-1) := by
    rw [show L-2 = (L-3)+1 by omega,
      show 2*k-1 = 2*(k-1)+1 by omega]
    exact binDec_odd (L-3) (k-1) (by omega)
  have h4 : binDec (L-3) (k-1) =
      d1 ++ binDec (L-4) (k/2) := by
    rw [show L-3 = (L-4)+1 by omega, hdiv]
    exact binDec_even (L-4) (k/2) hk2
  rw [h1,h2,h3,h4]
  simp [List.append_assoc]

private theorem m1ZeroOddSourceLeftFacing (a : Nat) :
    s1LeftFacing 4 8 1 a 0 =
      d1pow a ++ [true] ++ m1ZeroOddSourceLeftSuffix := by
  simp [s1LeftFacing, m1ZeroOddSourceLeftSuffix,
    markerWord, binDec_four_eight, List.append_assoc]

private theorem m1ZeroOddBaseLeftOnes
    (a b : Nat) (h : Int) :
    leftOnes (s1Config 4 8 1 a 0 b h).tape h (3*a+1) := by
  intro i hi
  have hcell := s1Config_left_cell 4 8 1 a 0 b h i
  have hface := m1ZeroOddSourceLeftFacing a
  have hside := sideBit_d1pow_append a i
    ([true] ++ m1ZeroOddSourceLeftSuffix) (by simp [d1pow_length]; omega)
  rw [hface, hside] at hcell
  have hc : i < 3*a ∨ i = 3*a := by omega
  rcases hc with hlt | heq
  · simp [sideBit_d1pow, hlt] at hcell ⊢
  · subst i
    simp [sideBit] at hcell ⊢

private theorem m1ZeroOddSweptLeftCell
    (a b : Nat) (h : Int) (i : Nat) :
    sweptLeft (3*a+1) (s1Config 4 8 1 a 0 b h).tape h
      (h - ((3*a+1+i : Nat) : Int)) =
      sideBit m1ZeroOddSourceLeftSuffix i := by
  let T := (s1Config 4 8 1 a 0 b h).tape
  have hcell := s1Config_left_cell 4 8 1 a 0 b h (3*a+1+i)
  have hface := m1ZeroOddSourceLeftFacing a
  have hside1 := sideBit_d1pow_append a (3*a+1+i)
    ([true] ++ m1ZeroOddSourceLeftSuffix) (by simp [d1pow_length]; omega)
  have hside2 := sideBit_append_right [true] m1ZeroOddSourceLeftSuffix
    (1+i) (by simp)
  have hpres := sweptLeft_preserves_left (3*a+1) T h
    (h - ((3*a+1+i : Nat) : Int)) (by omega)
  rw [hface, hside1, hside2] at hcell
  simpa [T] using hpres.trans hcell

private theorem m1ZeroOddSourceLeftBridgeBit
    (i : Nat) (hi : i ≤ 15) :
    sideBit m1ZeroOddSourceLeftSuffix i =
      decide (-(i : Int) ∈ m1ZeroOddBridgeStart.marked) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
      i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hc with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h <;> subst i <;>
    simp [m1ZeroOddSourceLeftSuffix, m1ZeroOddBridgeStart,
      markerWord, d0, d1, lh, sideBit]

private theorem m1ZeroOddBridge_input_match
    (a b : Nat) (h : Int)
    (hOn : leftOnes (s1Config 4 8 1 a 0 b h).tape h (3*a+1)) :
    ∀ y, m1ZeroOddBridgeInside y = true →
      sweptLeft (3*a+1) (s1Config 4 8 1 a 0 b h).tape h
        (h - ((3*a+1 : Nat) : Int) + y) =
        decide (y ∈ m1ZeroOddBridgeStart.marked) := by
  intro y hy
  have hyb : -15 ≤ y ∧ y ≤ 2 := by
    simpa [m1ZeroOddBridgeInside] using hy
  by_cases hy0 : y ≤ 0
  · let i : Nat := Int.toNat (-y)
    have hiCast : (i : Int) = -y := by
      simp [i]
      omega
    have hi : i ≤ 15 := by omega
    have hcoord :
        h - ((3*a+1 : Nat) : Int) + y =
          h - ((3*a+1+i : Nat) : Int) := by
      rw [hiCast]
      push_cast
      omega
    rw [hcoord]
    rw [m1ZeroOddSweptLeftCell a b h i]
    rw [m1ZeroOddSourceLeftBridgeBit i hi]
    simp [hiCast]
  · have hypos : y = 1 ∨ y = 2 := by omega
    rcases hypos with rfl | rfl
    · have hleft := sweptLeft_leftmost (3*a)
        (s1Config 4 8 1 a 0 b h).tape h
      simpa using hleft
    · have hblock := sweptLeft_block (3*a+1) (3*a-1)
        (s1Config 4 8 1 a 0 b h).tape h (by omega) hOn
      simpa using hblock

/-- The base q4 cut tape for the odd-quotient n=8 case. -/
def m1ZeroOddBaseCutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 4 8 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN := h - (N : Int)
  (frameAt T1 hN m1ZeroOddBridgeInside m1ZeroOddBridgeEnd).tape

private theorem m1ZeroOddBaseCutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m1ZeroOddBridgeInside (x - (h - ((3*a+1 : Nat) : Int))) = false) :
    m1ZeroOddBaseCutTape a b h x =
      sweptLeft (3*a+1) (s1Config 4 8 1 a 0 b h).tape h x := by
  simp [m1ZeroOddBaseCutTape, frameAt_tape_outside, hout]

private theorem m1ZeroOddBaseCutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m1ZeroOddBridgeInside (x - (h - ((3*a+1 : Nat) : Int))) = true) :
    m1ZeroOddBaseCutTape a b h x =
      decide ((x - (h - ((3*a+1 : Nat) : Int))) ∈
        m1ZeroOddBridgeEnd.marked) := by
  simp [m1ZeroOddBaseCutTape, frameAt_tape_inside, hin]

private theorem m1ZeroOddLeftFacingPrefixTrue (a i : Nat)
    (hi : i ≤ 3*a) :
    sideBit (m1ZeroOddQ4LeftFacing 4 7 a) i = true := by
  have hface :
      m1ZeroOddQ4LeftFacing 4 7 a =
        [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec 4 7 ++ lh := by
    rfl
  rw [hface]
  have hlen : ([true] ++ d1pow a).length = 3*a+1 := by
    simp [d1pow_length]
  have hlt : i < ([true] ++ d1pow a).length := by
    omega
  rw [sideBit_append_left]
  · simp [sideBit_d1pow, hi]
  · simpa [hlen] using hlt

private theorem m1ZeroOddLeftFacingBridgeBit
    (a j : Nat) (hj : j ≤ 15) :
    sideBit (m1ZeroOddQ4LeftFacing 4 7 a) (3*a+1+j) =
      decide (-(j : Int) ∈ m1ZeroOddBridgeEnd.marked) := by
  have hface :
      m1ZeroOddQ4LeftFacing 4 7 a =
        [true] ++ d1pow a ++
          (markerWord 0 ++ d0 ++ binDec 4 7 ++ lh) := by
    rfl
  have hlen : ([true] ++ d1pow a).length = 3*a+1 := by
    simp [d1pow_length]
  rw [hface, sideBit_append_right]
  · have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
        j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
    rcases hc with h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h <;> subst j <;>
      simp [markerWord, d0, d1, binDec_four_seven, lh,
        m1ZeroOddBridgeEnd, sideBit]
  · simpa [hlen] using (show 3*a+1 ≤ 3*a+1+j by omega)

private theorem m1ZeroOddLeftFacingTail
    (a i : Nat) (hi : 3*a+17 ≤ i) :
    sideBit (s1LeftFacing 4 8 1 a 0) i =
      sideBit (m1ZeroOddQ4LeftFacing 4 7 a) i := by
  let shared : List Bool := [true] ++ lh
  let sourcePrefix : List Bool :=
    d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d1 ++ d1 ++ [false, false]
  let targetPrefix : List Bool :=
    [true] ++ d1pow a ++ markerWord 0 ++ d0 ++
      d0 ++ d0 ++ d0 ++ [true, true]
  have hsource :
      s1LeftFacing 4 8 1 a 0 = sourcePrefix ++ shared := by
    simp [sourcePrefix, shared, s1LeftFacing,
      markerWord, binDec_four_eight, d0, d1, lh, List.append_assoc]
  have htarget :
      m1ZeroOddQ4LeftFacing 4 7 a = targetPrefix ++ shared := by
    simp [targetPrefix, shared, q4LeftFacing,
      markerWord, binDec_four_seven, d0, d1, lh, List.append_assoc]
  have hsourceLen : sourcePrefix.length = 3*a+17 := by
    simp [sourcePrefix, d1pow_length, markerWord]
  have htargetLen : targetPrefix.length = 3*a+17 := by
    simp [targetPrefix, d1pow_length, markerWord]
  rw [hsource, htarget]
  rw [sideBit_append_right sourcePrefix shared i]
  rw [sideBit_append_right targetPrefix shared i]
  simp [hsourceLen, htargetLen]
  omega

private theorem m1ZeroOddBaseCutTape_head
    (a b : Nat) (h : Int) (ha : 0 < a) :
    m1ZeroOddBaseCutTape a b h h = true := by
  have hOn := m1ZeroOddBaseLeftOnes a b h
  have hblock := sweptLeft_block (3*a+1) 0
    (s1Config 4 8 1 a 0 b h).tape h (by omega) hOn
  have hout : m1ZeroOddBridgeInside
      (h - (h - ((3*a+1 : Nat) : Int))) = false := by
    simp [m1ZeroOddBridgeInside]
    omega
  rw [m1ZeroOddBaseCutTape_eq_swept a b h h hout]
  simpa using hblock

private theorem m1ZeroOddBaseCutTape_leftFacing
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ i, m1ZeroOddBaseCutTape a b h (h - (i : Int)) =
      sideBit (m1ZeroOddQ4LeftFacing 4 7 a) i := by
  intro i
  by_cases hi : i ≤ 3*a-2
  · have hout : m1ZeroOddBridgeInside
        ((h - (i : Int)) - (h - ((3*a+1 : Nat) : Int))) = false := by
      simp [m1ZeroOddBridgeInside]
      omega
    rw [m1ZeroOddBaseCutTape_eq_swept a b h (h-(i:Int)) hout]
    have hOn := m1ZeroOddBaseLeftOnes a b h
    have hblock := sweptLeft_block (3*a+1) i
      (s1Config 4 8 1 a 0 b h).tape h (by omega) hOn
    have htrue := m1ZeroOddLeftFacingPrefixTrue a i (by omega)
    simpa using hblock.trans htrue.symm
  · by_cases hiLast : i = 3*a-1
    · have hin : m1ZeroOddBridgeInside
          ((h - (i : Int)) - (h - ((3*a+1 : Nat) : Int))) = true := by
        simp [m1ZeroOddBridgeInside]
        omega
      rw [m1ZeroOddBaseCutTape_eq_end_inside a b h (h-(i:Int)) hin]
      have hbit := m1ZeroOddLeftFacingPrefixTrue a i (by omega)
      simpa [m1ZeroOddBridgeEnd] using hbit
    · by_cases hiLast2 : i = 3*a
      · have hin : m1ZeroOddBridgeInside
            ((h - (i : Int)) - (h - ((3*a+1 : Nat) : Int))) = true := by
          simp [m1ZeroOddBridgeInside]
          omega
        rw [m1ZeroOddBaseCutTape_eq_end_inside a b h (h-(i:Int)) hin]
        have hbit := m1ZeroOddLeftFacingPrefixTrue a i (by omega)
        simpa [m1ZeroOddBridgeEnd] using hbit
      · by_cases hiBridge : i ≤ 3*a+16
        · let j := i - (3*a+1)
          have hj : j ≤ 15 := by dsimp [j]; omega
          have hin : m1ZeroOddBridgeInside
              ((h - (i : Int)) - (h - ((3*a+1 : Nat) : Int))) = true := by
            simp [m1ZeroOddBridgeInside, j]
            omega
          rw [m1ZeroOddBaseCutTape_eq_end_inside a b h (h-(i:Int)) hin]
          have hbit := m1ZeroOddLeftFacingBridgeBit a j hj
          have hidx : 3*a+1+j = i := by dsimp [j]; omega
          rw [← hidx]
          have hcoord : -((j : Int)) =
              (h - (i : Int)) - (h - ((3*a+1 : Nat) : Int)) := by
            dsimp [j]
            omega
          simpa [hcoord] using hbit
        · have htail := m1ZeroOddLeftFacingTail a i (by omega)
          have hout : m1ZeroOddBridgeInside
              ((h - (i : Int)) - (h - ((3*a+1 : Nat) : Int))) = false := by
            simp [m1ZeroOddBridgeInside]
            omega
          rw [m1ZeroOddBaseCutTape_eq_swept a b h (h-(i:Int)) hout]
          have hpres := sweptLeft_preserves_left (3*a+1)
            (s1Config 4 8 1 a 0 b h).tape h (h-(i:Int)) (by omega)
          have hcell := s1Config_left_cell 4 8 1 a 0 b h i
          rw [hpres, hcell, htail]

private theorem m1ZeroOddBaseCutTape_rightFacing
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ i, m1ZeroOddBaseCutTape a b h (h + 1 + (i : Int)) =
      sideBit (q4RightFacing b) i := by
  intro i
  by_cases hi : i = 0
  · subst i
    have hout : m1ZeroOddBridgeInside
        ((h+1) - (h - ((3*a+1 : Nat) : Int))) = false := by
      simp [m1ZeroOddBridgeInside]
      omega
    rw [m1ZeroOddBaseCutTape_eq_swept a b h (h+1) hout]
    have hplus := sweptLeft_plus1 (3*a)
      (s1Config 4 8 1 a 0 b h).tape h
    simpa using hplus
  · have hiPos : 0 < i := by omega
    have hout : m1ZeroOddBridgeInside
        ((h+1+(i:Int)) - (h - ((3*a+1 : Nat) : Int))) = false := by
      simp [m1ZeroOddBridgeInside]
      omega
    rw [m1ZeroOddBaseCutTape_eq_swept a b h (h+1+(i:Int)) hout]
    have hpres := sweptLeft_preserves_right (3*a+1)
      (s1Config 4 8 1 a 0 b h).tape h (h+1+(i:Int)) (by omega)
    have hcell := s1Config_right_cell 4 8 1 a 0 b h i
    have hsucc := q4RightFacing_succ b (i-1)
    rw [hpres, hcell]
    simpa [Nat.sub_add_cancel hiPos] using hsucc

private theorem m1ZeroOddRightShape_of_stream
    (T : Int → Bool) (h : Int) (b : Nat)
    (hhead : T h = true)
    (hright : ∀ i, T (h+1+(i:Int)) = sideBit (q4RightFacing b) i) :
    q4RightShape T h b := by
  unfold q4RightShape
  refine ⟨hhead, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hbit := hright (i+1)
    simpa [q4RightFacing, sideBit] using hbit
  · have hbit := hright 4
    simpa [q4RightFacing, sideBit] using hbit
  · have hbit := hright 5
    simpa [q4RightFacing, sideBit] using hbit
  · intro i hi
    have hbit := hright (6+i)
    simpa [q4RightFacing, sideBit] using hbit
  · intro i hi
    have hbit := hright (9+3*b+i)
    simpa [q4RightFacing, sideBit] using hbit

/-- The base n=8, marker-1 source prefix reaches a q4 cut. -/
theorem m1ZeroOddBase_q4_prefix_data
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (64+12*a) (s1Config 4 8 1 a 0 b h) =
        some ⟨4, h, m1ZeroOddBaseCutTape a b h⟩ ∧
      (∀ i, m1ZeroOddBaseCutTape a b h (h-(i:Int)) =
        sideBit (m1ZeroOddQ4LeftFacing 4 7 a) i) ∧
      q4RightShape (m1ZeroOddBaseCutTape a b h) h b ∧
      (∀ i, m1ZeroOddBaseCutTape a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i) := by
  let T := (s1Config 4 8 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN := h - (N : Int)
  let T2 := (frameAt T1 hN m1ZeroOddBridgeInside m1ZeroOddBridgeEnd).tape
  have hface := m1ZeroOddSourceLeftFacing a
  have hOn := m1ZeroOddBaseLeftOnes a b h
  have hRight : T (h+1) = false := by
    have hcell := s1Config_right_cell 4 8 1 a 0 b h 0
    simpa [s0RightFacing, sideBit] using hcell
  have hSweep :
      run tm2 (3*N) (s1Config 4 8 1 a 0 b h) =
        some ⟨3, hN, T1⟩ := by
    simpa [N, T, T1, hN] using counted_left_sweep N T h hOn hRight
  have hInput := m1ZeroOddBridge_input_match a b h hOn
  have hBridgeHeads : ∀ k < 62,
      m1ZeroOddBridgeInside
        ((fRun tm2 k m1ZeroOddBridgeStart).getD m1ZeroOddBridgeStart).head = true := by
    intro k hk
    have hall := List.all_eq_true.mp m1ZeroOddBridge_heads k
      (by simp [List.mem_range, hk])
    simpa using hall
  have hBridge :
      run tm2 62 ⟨3, hN, T1⟩ =
        some ⟨4, hN+2, T2⟩ := by
    have hb := bridgeAt T1 hN m1ZeroOddBridgeInside
      m1ZeroOddBridgeStart m1ZeroOddBridgeEnd 62 rfl
      m1ZeroOddBridge_exact hBridgeHeads hInput
    simpa [T2, frameAt_head] using hb
  have hlinear : linearRightOnes T2 (hN+2) (3*a-1) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hin : m1ZeroOddBridgeInside ((hN+2)-hN) = true := by
        simp [m1ZeroOddBridgeInside]
      have hbit := frameAt_tape_inside T1 hN
        m1ZeroOddBridgeInside m1ZeroOddBridgeEnd (hN+2) hin
      simpa [T2, m1ZeroOddBridgeEnd] using hbit
    · have hj : i ≤ 3*a-2 := by omega
      let j := 3*a-1-i
      have hj0 : j+1 < N := by dsimp [j, N]; omega
      have hblock := sweptLeft_block N j T h hj0 hOn
      have hout : m1ZeroOddBridgeInside ((hN+2+(i:Int))-hN) = false := by
        simp [m1ZeroOddBridgeInside]
        omega
      have houtside := frameAt_tape_outside T1 hN
        m1ZeroOddBridgeInside m1ZeroOddBridgeEnd (hN+2+(i:Int)) hout
      have hcoord : hN+2+(i:Int) = h-(j:Int) := by
        dsimp [j, N, hN]
        omega
      rw [hcoord] at houtside
      simpa [T2,m1ZeroOddBaseCutTape] using houtside.trans hblock
  have hscanHead : hN+2+(3*a-1 : Nat) = h := by
    dsimp [N, hN]
    omega
  have hScan :
      run tm2 (3*a-1) ⟨4, hN+2, T2⟩ =
        some ⟨4, h, T2⟩ := by
    simpa [hscanHead] using E_scan T2 (hN+2) (3*a-1) hlinear
  have hRun := run_append hSweep hBridge
  have hRun := run_append hRun hScan
  have hsteps : 3*(3*a+1)+62+(3*a-1) = 64+12*a := by omega
  have hRun :
      run tm2 (64+12*a) (s1Config 4 8 1 a 0 b h) =
        some ⟨4, h, T2⟩ := by
    simpa [N, T, T1, T2, hN, hsteps] using hRun
  have hleft := m1ZeroOddBaseCutTape_leftFacing a b h ha
  have hright := m1ZeroOddBaseCutTape_rightFacing a b h ha
  have hhead := m1ZeroOddBaseCutTape_head a b h ha
  have hshape := m1ZeroOddRightShape_of_stream
    (m1ZeroOddBaseCutTape a b h) h b hhead hright
  refine ⟨?_, hleft, hshape, hright⟩
  simpa [m1ZeroOddBaseCutTape, T2] using hRun



/-! ## General odd-quotient lift

The finite bridge only reads the first four low-order BinDec blocks.  For
odd k, both 8k and 8k-1 have a common quotient tail after those four blocks.
We lift the n=8 source prefix over the half-line it actually visits.
-/

/-- The first 3a+17 cells of the m=1, n=8k input left word. -/
private def m1ZeroOddResidue0InputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d1 ++ d1 ++ [false,false]

/-- The first 3a+17 cells of the q4 cut left word for the n=8k row. -/
private def m1ZeroOddResidue0TargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++
    d0 ++ d0 ++ d0 ++ [true,true]

/-- The source/target half-line used to transport the fixed n=8 bridge. -/
def m1ZeroOddResidue0Inside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+1:Int))-15 ≤ x)

/-- Marker-zero q4 left stream after the generalized n=8k prefix. -/
def m1ZeroOddResidue0LeftFacing (L k a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L (8*k-1) ++ lh

/-- The generalized cut tape is the fixed n=8 output on the read half-line,
and the original n=8k input everywhere to its left. -/
def m1ZeroOddResidue0CutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m1ZeroOddResidue0Inside a h)
    (s1Config L (8*k) 1 a 0 b h).tape
    (⟨4,h,m1ZeroOddBaseCutTape a b h⟩ : Config)).tape

private theorem m1ZeroOddResidue0_config_ext_by_fields (c d : Config)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      cases hstate
      cases hhead
      cases htape
      rfl

private theorem m1ZeroOddResidue0_input_left
    (L k a : Nat) (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) :
    s1LeftFacing L (8*k) 1 a 0 =
      m1ZeroOddResidue0InputPrefix a ++
        ([true] ++ binDec (L-4) (k/2) ++ lh) := by
  have hbin := m1ZeroOdd_binDec_residue8 L k hL hkodd hbound
  simp [s1LeftFacing,m1ZeroOddResidue0InputPrefix,
    markerWord,hbin,d0,d1,List.append_assoc]

private theorem m1ZeroOddResidue0_base_input_left (a : Nat) :
    s1LeftFacing 4 8 1 a 0 =
      m1ZeroOddResidue0InputPrefix a ++ ([true] ++ lh) := by
  simp [s1LeftFacing,m1ZeroOddResidue0InputPrefix,
    markerWord,binDec_four_eight,d0,d1,List.append_assoc]

private theorem m1ZeroOddResidue0_target_left
    (L k a : Nat) (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) :
    m1ZeroOddResidue0LeftFacing L k a =
      m1ZeroOddResidue0TargetPrefix a ++
        ([true] ++ binDec (L-4) (k/2) ++ lh) := by
  have hbin := m1ZeroOdd_binDec_residue7 L k hL hkodd hbound
  simp [m1ZeroOddResidue0LeftFacing,m1ZeroOddResidue0TargetPrefix,
    markerWord,hbin,d0,d1,List.append_assoc]

private theorem m1ZeroOddResidue0_base_target_left (a : Nat) :
    m1ZeroOddQ4LeftFacing 4 7 a =
      m1ZeroOddResidue0TargetPrefix a ++ ([true] ++ lh) := by
  simp [m1ZeroOddQ4LeftFacing,m1ZeroOddResidue0TargetPrefix,
    markerWord,binDec_four_seven,d0,d1,List.append_assoc]

private theorem m1ZeroOddResidue0_inputPrefix_length (a : Nat) :
    (m1ZeroOddResidue0InputPrefix a).length = 3*a+17 := by
  simp [m1ZeroOddResidue0InputPrefix,d1pow_length,markerWord,d0,d1]

private theorem m1ZeroOddResidue0_targetPrefix_length (a : Nat) :
    (m1ZeroOddResidue0TargetPrefix a).length = 3*a+17 := by
  simp [m1ZeroOddResidue0TargetPrefix,d1pow_length,markerWord,d0,d1]

/-- The general and n=8 source tapes agree on every cell the prefix reads. -/
private theorem m1ZeroOddResidue0_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1) (hbound : 8*k < 2^L) :
    ∀ x, m1ZeroOddResidue0Inside a h x = true →
      (s1Config L (8*k) 1 a 0 b h).tape x =
      (s1Config 4 8 1 a 0 b h).tape x := by
  have hsourceLeft :=
    m1ZeroOddResidue0_input_left L k a hL hkodd hbound
  have hbaseLeft := m1ZeroOddResidue0_base_input_left a
  have hprefixLength := m1ZeroOddResidue0_inputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i : Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a+1:Int))-15 ≤ x := by
      simpa [m1ZeroOddResidue0Inside] using hx
    have hi : i ≤ 3*a+16 := by omega
    have hiPrefix : i < (m1ZeroOddResidue0InputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*k) 1 a 0 b h i
    have hbase := s1Config_left_cell 4 8 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left
      (m1ZeroOddResidue0InputPrefix a)
      ([true] ++ binDec (L-4) (k/2) ++ lh) i hiPrefix
    have hbaseBit := sideBit_append_left
      (m1ZeroOddResidue0InputPrefix a) ([true] ++ lh) i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i : Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*k) 1 a 0 b h i
    have hbase := s1Config_right_cell 4 8 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm


private theorem m1ZeroOdd_sweptLeft_head_eq_source (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft q T h (h-(q:Int)) = T (h-(q:Int)) := by
  induction q with
  | zero => simp [sweptLeft]
  | succ q ih =>
      have hcoord : h-((q+1:Int)) = (h-1)-(q:Int) := by omega
      rw [show sweptLeft (q+1) T h =
        sweptLeft q (holeThree T h) (h-1) by rfl]
      rw [hcoord,ih]
      have hne1 : h-((q+1:Int)) ≠ h+1 := by omega
      have hne2 : h-((q+1:Int)) ≠ h := by omega
      simp [holeThree,hne1,hne2]

private theorem m1ZeroOdd_sweptLeft_head_plus1_false (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft (q+1) T h (h-(q:Int)) = false := by
  induction q with
  | zero => simp [sweptLeft,holeThree]
  | succ q ih =>
      have hcoord : h-((q+1:Int)) = (h-1)-(q:Int) := by omega
      rw [show sweptLeft (q+2) T h =
        sweptLeft (q+1) (holeThree T h) (h-1) by rfl]
      rw [hcoord]
      exact ih (holeThree T h) (h-1)

private theorem m1ZeroOdd_leftSweep_one (T : Int → Bool) (h : Int)
    (ht : T h = true) :
    run tm2 1 ⟨3,h,T⟩ = some ⟨1,h+1,T⟩ := by
  simp [run,rawStep,readSlot,applyMove,tm2,ht]

private theorem m1ZeroOdd_leftSweep_two (T : Int → Bool) (h : Int)
    (ht : T h = true) (hr : T (h+1) = false) :
    run tm2 2 ⟨3,h,T⟩ =
      some ⟨2,h,(fun x => if x = h+1 then true else T x)⟩ := by
  rw [show 2 = 1+1 by omega,run_append,
    m1ZeroOdd_leftSweep_one T h ht]
  simp [run,rawStep,readSlot,applyMove,tm2,hr]

private theorem m1ZeroOdd_counted_left_sweep_heads
    (N : Nat) (T : Int → Bool) (h : Int)
    (hOn : leftOnes T h N) (hr : T (h+1) = false)
    (k : Nat) (hk : k < 3*N) (d : Config)
    (hd : run tm2 k ⟨3,h,T⟩ = some d) :
    h-(N:Int) ≤ d.head := by
  let q := k/3
  let r := k%3
  have hkdecomp : k = 3*q+r := by dsimp [q,r]; omega
  have hq : q < N := by dsimp [q]; omega
  have hqOn : leftOnes T h q := by
    intro i hi
    exact hOn i (by omega)
  have hqrun := counted_left_sweep q T h hqOn hr
  let Tq := sweptLeft q T h
  have hqhead : Tq (h-(q:Int)) = true := by
    rw [show Tq = sweptLeft q T h by rfl,
      m1ZeroOdd_sweptLeft_head_eq_source]
    exact hOn q hq
  have hqright : Tq (h-(q:Int)+1) = false := by
    by_cases hq0 : q = 0
    · subst q
      simpa [Tq] using hr
    · obtain ⟨q',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      have hfalse := m1ZeroOdd_sweptLeft_head_plus1_false q' T h
      simpa [Tq] using hfalse
  have hqrun' :
      run tm2 (3*q) ⟨3,h,T⟩ =
        some ⟨3,h-(q:Int),Tq⟩ := by
    simpa [Tq] using hqrun
  rw [hkdecomp,run_append,hqrun'] at hd
  simp only [Option.bind_some] at hd
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by
    have hrlt : r < 3 := Nat.mod_lt _ (by decide)
    omega
  rcases hrCases with hr0|hr1|hr2
  · subst r
    simp [run] at hd
    have heq := Option.some.inj hd
    subst d
    simp
    omega
  · subst r
    rw [m1ZeroOdd_leftSweep_one Tq (h-(q:Int)) hqhead] at hd
    have heq := Option.some.inj hd
    subst d
    simp
    omega
  · subst r
    rw [m1ZeroOdd_leftSweep_two Tq (h-(q:Int)) hqhead hqright] at hd
    have heq := Option.some.inj hd
    subst d
    simp
    omega

private theorem m1ZeroOdd_fRun_prefix_exists {m c n k d}
    (h : fRun m n c = some d) (hk : k ≤ n) :
    ∃ e, fRun m k c = some e := by
  induction n generalizing k c d with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      exact ⟨c,by simpa [fRun] using h⟩
  | succ n ih =>
      have h' : (fRun m n c).bind (fStep m) = some d := by
        simpa [fRun] using h
      cases hp : fRun m n c with
      | none => simp [hp] at h'
      | some e =>
          by_cases hk' : k ≤ n
          · exact ih hp hk'
          · have hkEq : k = n+1 := by omega
            subst k
            exact ⟨d,h⟩

private theorem m1ZeroOdd_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m1ZeroOddBridgeInside y = true →
      T (h+y) = decide (y ∈ m1ZeroOddBridgeStart.marked))
    (j : Nat) (hj : j < 62) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-15 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    m1ZeroOdd_fRun_prefix_exists m1ZeroOddBridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m1ZeroOddBridgeStart with
        | none => true
        | some f => m1ZeroOddBridgeInside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk62 : k < 62 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m1ZeroOddBridge_heads) k
      (List.mem_range.mpr hk62)
  have hbridge := bridgeAt T h m1ZeroOddBridgeInside
    m1ZeroOddBridgeStart e j rfl hexact hcheckj hmatch
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m1ZeroOddBridgeInside e :=
    Option.some.inj hd
  have hinside : m1ZeroOddBridgeInside e.head = true := by
    have hh := (List.all_eq_true.mp m1ZeroOddBridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -15 ≤ e.head := by
    simp [m1ZeroOddBridgeInside] at hinside
    omega
  rw [hdeq]
  simp [frameAt_head]
  omega

private theorem m1ZeroOdd_E_scan_prefix_head
    (T : Int → Bool) (h : Int) (n : Nat)
    (hlinear : linearRightOnes T h n)
    (j : Nat) (hj : j < n) (d : Config)
    (hd : run tm2 j ⟨4,h,T⟩ = some d) :
    d.head = h+(j:Int) := by
  have hlinearJ : linearRightOnes T h j := by
    intro i hi
    exact hlinear i (by omega)
  have hrun := E_scan T h j hlinearJ
  rw [hrun] at hd
  have heq := Option.some.inj hd
  simp at heq
  omega

private theorem m1ZeroOddBase_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ k, k < 64+12*a → ∀ d,
      run tm2 k (s1Config 4 8 1 a 0 b h) = some d →
      h-((3*a+1:Int))-15 ≤ d.head := by
  let T := (s1Config 4 8 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m1ZeroOddBaseCutTape a b h
  have hOn := m1ZeroOddBaseLeftOnes a b h
  have hRight : T (h+1) = false := by
    have hcell := s1Config_right_cell 4 8 1 a 0 b h 0
    simpa [s0RightFacing,sideBit] using hcell
  have hSweep :
      run tm2 (3*N) (s1Config 4 8 1 a 0 b h) =
        some ⟨3,hN,T1⟩ := by
    simpa [N,T,T1,hN] using counted_left_sweep N T h hOn hRight
  have hInput := m1ZeroOddBridge_input_match a b h hOn
  have hBridgeHeads : ∀ k < 62,
      m1ZeroOddBridgeInside
        ((fRun tm2 k m1ZeroOddBridgeStart).getD m1ZeroOddBridgeStart).head = true := by
    intro k hk
    have hall := List.all_eq_true.mp m1ZeroOddBridge_heads k
      (by simp [List.mem_range,hk])
    simpa using hall
  have hBridge :
      run tm2 62 ⟨3,hN,T1⟩ =
        some ⟨4,hN+2,T2⟩ := by
    have hb := bridgeAt T1 hN m1ZeroOddBridgeInside
      m1ZeroOddBridgeStart m1ZeroOddBridgeEnd 62 rfl
      m1ZeroOddBridge_exact hBridgeHeads hInput
    simpa [T2,m1ZeroOddBaseCutTape,frameAt_head] using hb
  have hlinear : linearRightOnes T2 (hN+2) (3*a-1) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hin : m1ZeroOddBridgeInside ((hN+2)-hN) = true := by
        simp [m1ZeroOddBridgeInside]
      have hbit := frameAt_tape_inside T1 hN
        m1ZeroOddBridgeInside m1ZeroOddBridgeEnd (hN+2) hin
      simpa [T2,m1ZeroOddBaseCutTape,m1ZeroOddBridgeEnd] using hbit
    · have hj : i ≤ 3*a-2 := by omega
      let j := 3*a-1-i
      have hj0 : j+1 < N := by dsimp [j,N]; omega
      have hblock := sweptLeft_block N j T h hj0 hOn
      have hout : m1ZeroOddBridgeInside ((hN+2+(i:Int))-hN) = false := by
        simp [m1ZeroOddBridgeInside]
        omega
      have houtside := frameAt_tape_outside T1 hN
        m1ZeroOddBridgeInside m1ZeroOddBridgeEnd (hN+2+(i:Int)) hout
      have hcoord : hN+2+(i:Int) = h-(j:Int) := by
        dsimp [j,N,hN]
        omega
      rw [hcoord] at houtside
      simpa [T2,m1ZeroOddBaseCutTape] using houtside.trans hblock
  have hBridge' :
      run tm2 62 ⟨3,hN,T1⟩ = some ⟨4,hN+2,T2⟩ := hBridge
  have hScan :
      run tm2 (3*a-1) ⟨4,hN+2,T2⟩ =
        some ⟨4,h,T2⟩ := by
    have hscanHead : hN+2+(3*a-1 : Nat) = h := by
      dsimp [N,hN]
      omega
    simpa [hscanHead] using E_scan T2 (hN+2) (3*a-1) hlinear
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+62
  by_cases hk1 : k < p1
  · have hd' : run tm2 k ⟨3,h,T⟩ = some d := by simpa [T] using hd
    have hlow := m1ZeroOdd_counted_left_sweep_heads N T h hOn hRight k
      (by dsimp [p1,N] at *; omega) d hd'
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j < 62 := by dsimp [j,p1,p2] at *; omega
      have hkEq : k = p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_append,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m1ZeroOdd_bridge_prefix_lower T1 hN hInput j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j < 3*a-1 := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k = p1+(62+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_append,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_append,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := m1ZeroOdd_E_scan_prefix_head T2 (hN+2) (3*a-1) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

/-- Lift the exact 64+12a n=8 prefix to every admissible n=8k with odd k. -/
theorem m1ZeroOdd_residue0_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    run tm2 (64+12*a) (s1Config L (8*k) 1 a 0 b h) =
      some ⟨4,h,m1ZeroOddResidue0CutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 4 8 1 a 0 b h).tape⟩
  let background := (s1Config L (8*k) 1 a 0 b h).tape
  have hinput := m1ZeroOddResidue0_input_matches L k a b h hL hkodd hbound
  have hstart :
      frame (m1ZeroOddResidue0Inside a h) background base =
        s1Config L (8*k) 1 a 0 b h := by
    apply m1ZeroOddResidue0_config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m1ZeroOddResidue0Inside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 64+12*a → ∀ d,
        run tm2 j base = some d →
        m1ZeroOddResidue0Inside a h d.head = true := by
    intro j hj d hd
    have hd' : run tm2 j (s1Config 4 8 1 a 0 b h) = some d := by
      simpa [base] using hd
    have hlow := m1ZeroOddBase_prefix_head_bound a b h ha j hj d hd'
    simpa [m1ZeroOddResidue0Inside] using hlow
  have hlift := run_frame tm2
    (m1ZeroOddResidue0Inside a h) background base (64+12*a) hheads
  rw [hstart] at hlift
  obtain ⟨hprefix,hleft,hshape,hright⟩ :=
    m1ZeroOddBase_q4_prefix_data a b h ha
  rw [hprefix] at hlift
  simp only [Option.map_some] at hlift
  simpa [m1ZeroOddResidue0CutTape,background] using hlift




private theorem m1ZeroOddResidue0_cut_eq_base
    (L k a b : Nat) (h x : Int)
    (hin : m1ZeroOddResidue0Inside a h x = true) :
    m1ZeroOddResidue0CutTape L k a b h x =
      m1ZeroOddBaseCutTape a b h x := by
  simp [m1ZeroOddResidue0CutTape,frame,hin]

private theorem m1ZeroOddResidue0_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m1ZeroOddResidue0Inside a h x = false) :
    m1ZeroOddResidue0CutTape L k a b h x =
      (s1Config L (8*k) 1 a 0 b h).tape x := by
  simp [m1ZeroOddResidue0CutTape,frame,hout]

private theorem m1ZeroOddResidue0_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    ∀ i, m1ZeroOddResidue0CutTape L k a b h (h-(i:Int)) =
      sideBit (m1ZeroOddResidue0LeftFacing L k a) i := by
  obtain ⟨_,hbaseLeft,_,_⟩ :=
    m1ZeroOddBase_q4_prefix_data a b h ha
  have hbaseTarget := m1ZeroOddResidue0_base_target_left a
  have htarget :=
    m1ZeroOddResidue0_target_left L k a hL hkodd hbound
  have hsource :=
    m1ZeroOddResidue0_input_left L k a hL hkodd hbound
  have hinputLen := m1ZeroOddResidue0_inputPrefix_length a
  have htargetLen := m1ZeroOddResidue0_targetPrefix_length a
  intro i
  by_cases hi : i ≤ 3*a+16
  · have hin :
        m1ZeroOddResidue0Inside a h (h-(i:Int)) = true := by
      simp [m1ZeroOddResidue0Inside]
      omega
    rw [m1ZeroOddResidue0_cut_eq_base L k a b h (h-(i:Int)) hin]
    rw [hbaseLeft i,hbaseTarget,htarget]
    have hbaseBit := sideBit_append_left
      (m1ZeroOddResidue0TargetPrefix a) ([true] ++ lh) i
      (by rw [m1ZeroOddResidue0_targetPrefix_length]; omega)
    have htargetBit := sideBit_append_left
      (m1ZeroOddResidue0TargetPrefix a)
      ([true] ++ binDec (L-4) (k/2) ++ lh) i
      (by rw [m1ZeroOddResidue0_targetPrefix_length]; omega)
    rw [hbaseBit,htargetBit]
  · have hout :
        m1ZeroOddResidue0Inside a h (h-(i:Int)) = false := by
      simp [m1ZeroOddResidue0Inside]
      omega
    rw [m1ZeroOddResidue0_cut_eq_input L k a b h (h-(i:Int)) hout]
    rw [s1Config_left_cell L (8*k) 1 a 0 b h i]
    rw [hsource,htarget]
    have hinputBit := sideBit_append_right
      (m1ZeroOddResidue0InputPrefix a)
      ([true] ++ binDec (L-4) (k/2) ++ lh) i
      (by rw [hinputLen]; omega)
    have htargetBit := sideBit_append_right
      (m1ZeroOddResidue0TargetPrefix a)
      ([true] ++ binDec (L-4) (k/2) ++ lh) i
      (by rw [htargetLen]; omega)
    rw [hinputBit,htargetBit]
    rw [hinputLen,htargetLen]

private theorem m1ZeroOddResidue0_rightFacing
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    ∀ i, m1ZeroOddResidue0CutTape L k a b h (h+1+(i:Int)) =
      sideBit (q4RightFacing b) i := by
  obtain ⟨_,_,_,hright⟩ :=
    m1ZeroOddBase_q4_prefix_data a b h ha
  intro i
  have hin :
      m1ZeroOddResidue0Inside a h (h+1+(i:Int)) = true := by
    simp [m1ZeroOddResidue0Inside]
    omega
  rw [m1ZeroOddResidue0_cut_eq_base L k a b h
    (h+1+(i:Int)) hin]
  exact hright i

private theorem m1ZeroOdd_sideBit_ge_length
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          simp only [sideBit]
          apply ih
          simp at hi
          omega

private theorem m1ZeroOddResidue0_head
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    m1ZeroOddResidue0CutTape L k a b h h = true := by
  have hin : m1ZeroOddResidue0Inside a h h = true := by
    simp [m1ZeroOddResidue0Inside]
  rw [m1ZeroOddResidue0_cut_eq_base L k a b h h hin]
  exact m1ZeroOddBaseCutTape_head a b h ha

private theorem m1ZeroOddResidue0_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    q4RightShape (m1ZeroOddResidue0CutTape L k a b h) h b := by
  apply m1ZeroOddRightShape_of_stream
    (m1ZeroOddResidue0CutTape L k a b h) h b
    (m1ZeroOddResidue0_head L k a b h hL hkodd hbound ha)
    (m1ZeroOddResidue0_rightFacing L k a b h hL hkodd hbound ha)

private theorem m1ZeroOddResidue0_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    ∀ i, 9+3*b ≤ i →
      m1ZeroOddResidue0CutTape L k a b h (h+1+(i:Int)) = false := by
  have hright :=
    m1ZeroOddResidue0_rightFacing L k a b h hL hkodd hbound ha
  have hlen : (q4RightFacing b).length = 9+3*b := by
    simp [q4RightFacing,d1pow_length]
    omega
  intro i hi
  rw [hright i]
  exact m1ZeroOdd_sideBit_ge_length (q4RightFacing b) i (by rw [hlen]; exact hi)

/-- The generic marker-zero target left word is exactly the q4 suffix
interface, with the high-order quotient carried unchanged. -/
private theorem m1ZeroOddResidue0_target_left_identity
    (L k a b : Nat) :
    s1LeftFacing L (8*k-1) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1ZeroOddResidue0LeftFacing L k a).drop 1 := by
  unfold s1LeftFacing m1ZeroOddResidue0LeftFacing
  rw [binDec_pow2_sub_one]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc]

/-- Compose the generalized q4 suffix after the lifted n=8 prefix. -/
theorem m1ZeroOdd_residue0_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    run tm2 (103+12*a+3*b)
      (s1Config L (8*k) 1 a 0 b h) =
      some (s1Config L (8*k-1) 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m1ZeroOddResidue0CutTape L k a b h
  let sourceLeft := m1ZeroOddResidue0LeftFacing L k a
  have hprefix :=
    m1ZeroOdd_residue0_q4_prefix_source L k a b h hL hkodd hbound ha
  have hshape :=
    m1ZeroOddResidue0_rightShape L k a b h hL hkodd hbound ha
  have htail :=
    m1ZeroOddResidue0_far_tail L k a b h hL hkodd hbound ha
  have hleft :=
    m1ZeroOddResidue0_leftFacing L k a b h hL hkodd hbound ha
  have happend := m1ZeroOddResidue0_target_left_identity L k a b
  have hfullSuffix := q4_suffix_run_to_s1Config
    T h b L (8*k-1) 0 (a+b+2) (2^b-1) sourceLeft
    hshape htail hleft happend
  have hnumTotal : 103+12*a+3*b =
      (64+12*a)+(39+3*b) := by omega
  rw [hnumTotal,run_append,hprefix]
  simp only [Option.bind_some]
  exact hfullSuffix

/-- The complete original-TM2 counted increment for marker 1 and n=8k,
where k is odd. -/
theorem m1ZeroOdd_residue0_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 (8*k) a b)
      (s1Config L (8*k) 1 a 0 b h) =
      some (s1Config L (8*k-1) 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hvodd : v2 k = 0 :=
    v2_of_odd k (by omega)
  have hv2k : v2 (2*k) = 1 := by
    have hgt : 1 < 2*k := by omega
    have heven : (2*k)%2 = 0 := by omega
    have hdiv : (2*k)/2 = k := by omega
    simp [v2,hgt,heven,hdiv,hvodd]
  have hv4k : v2 (4*k) = 2 := by
    have hgt : 1 < 4*k := by omega
    have heven : (4*k)%2 = 0 := by omega
    have hdiv : (4*k)/2 = 2*k := by omega
    simp [v2,hgt,heven,hdiv,hv2k]
  have hv : v2 (8*k) = 3 := by
    have hgt : 1 < 8*k := by omega
    have heven : (8*k)%2 = 0 := by omega
    have hdiv : (8*k)/2 = 4*k := by omega
    simp [v2,hgt,heven,hdiv,hv4k]
  have hcost : resetPrefixCost 1 (8*k) a b =
      103+12*a+3*b := by
    simp [resetPrefixCost,hv]
    omega
  have hprefix := m1ZeroOdd_residue0_reset_prefix_source
    L k a b h hL hkodd hbound ha
  have hdrainBound := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k-1) 0 (a+b+2) b (h+5+3*b)
    (s1Config L (8*k) 1 a 0 b h)
    (resetPrefixCost 1 (8*k) a b)
    (by simpa [hcost] using hprefix)
    (by simpa [resetDelta] using hdrainBound)
  rw [proposedIncrementCost_decomp 1 (8*k) a b,hcost]
  exact hrun

#print axioms m1ZeroOdd_residue0_q4_prefix_source
#print axioms m1ZeroOdd_residue0_reset_prefix_source
#print axioms m1ZeroOdd_residue0_counted_increment_source


#print axioms m1ZeroOddBridge_exact
#print axioms m1ZeroOddBridge_heads
#print axioms m1ZeroOddBase_q4_prefix_data

end BB6Coverage.Agent48M1ZeroOddQ4Prefix
