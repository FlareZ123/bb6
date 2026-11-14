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
    sideBit (q4LeftFacing 4 7 a) i = true := by
  have hface :
      q4LeftFacing 4 7 a =
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
    sideBit (q4LeftFacing 4 7 a) (3*a+1+j) =
      decide (-(j : Int) ∈ m1ZeroOddBridgeEnd.marked) := by
  have hface :
      q4LeftFacing 4 7 a =
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
      sideBit (q4LeftFacing 4 7 a) i := by
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
      q4LeftFacing 4 7 a = targetPrefix ++ shared := by
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
      sideBit (q4LeftFacing 4 7 a) i := by
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
    ∃ Tq,
      run tm2 (64+12*a) (s1Config 4 8 1 a 0 b h) =
        some ⟨4, h, Tq⟩ ∧
      (∀ i, Tq (h-(i:Int)) = sideBit (q4LeftFacing 4 7 a) i) ∧
      q4RightShape Tq h b ∧
      (∀ i, Tq (h+1+(i:Int)) = sideBit (q4RightFacing b) i) := by
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
  have hBridge :
      run tm2 62 ⟨3, hN, T1⟩ =
        some ⟨4, hN+2, T2⟩ := by
    have hb := bridgeAt T1 hN m1ZeroOddBridgeInside
      m1ZeroOddBridgeStart m1ZeroOddBridgeEnd 62 rfl
      m1ZeroOddBridge_exact m1ZeroOddBridge_heads hInput
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
      simpa [T2] using houtside.trans hblock
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
  refine ⟨m1ZeroOddBaseCutTape a b h, ?_, hleft, hshape, hright⟩
  simpa [m1ZeroOddBaseCutTape, T2] using hRun

#print axioms m1ZeroOddBridge_exact
#print axioms m1ZeroOddBridge_heads
#print axioms m1ZeroOddBase_q4_prefix_data

end BB6Coverage.Agent48M1ZeroOddQ4Prefix
