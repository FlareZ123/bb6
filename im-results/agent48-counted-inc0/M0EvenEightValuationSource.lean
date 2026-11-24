import M0EvenEightValuationEncoding
import M0EvenEightValuationFixedPrefix
import M0EvenEightValuationMacros
import M0EvenEightValuationSweepFacts
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M0EvenEightValuationSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent48M0EvenEightQ4Bridge
open BB6Coverage.Agent48M0EvenEightQ4Prefix
open BB6Coverage.Agent48M0EvenEightValuationEncoding
open BB6Coverage.Agent48M0EvenEightValuationFixedPrefix
open BB6Coverage.Agent48M0EvenEightValuation
open BB6Coverage.Agent48M0EvenEightValuationSweepFacts

set_option maxHeartbeats 3000000

private theorem config_ext_local (c d : Config)
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp_all

private theorem sweptRight1_preserves_right_local
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : h+3*(n:Int) ≤ x) :
    sweptRight1 n T h x = T x := by
  induction n generalizing T h with
  | zero => simp [sweptRight1]
  | succ n ih =>
      simp only [sweptRight1]
      have hp := ih (afterRight1 T h) (h+3) (by omega)
      rw [hp]
      have hx0 : x ≠ h := by omega
      have hx1 : x ≠ h+1 := by omega
      have hx2 : x ≠ h+2 := by omega
      simp [afterRight1,hx0,hx1,hx2]

/-- The source suffix after the initial d1^a sweep, with the quotient
factored as q = (2*u+1)*2^t. -/
def m0EvenEightValuationSourceSuffix (t len u : Nat) : List Bool :=
  markerWord 0 ++ d0 ++ d1pow (3+t) ++ d0 ++ binDec len u ++ lh

/-- The first fourteen head-facing cells are independent of the valuation. -/
private theorem sourceSuffix_prefix14_match (t len u i : Nat)
    (hi : i ≤ 13) :
    sideBit (m0EvenEightValuationSourceSuffix t len u) i =
      decide ((-(i:Int)) ∈ m0EvenEightBridgeStart.marked) := by
  have hcases :
      i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨
      i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    <;> subst i
    <;> simp [m0EvenEightValuationSourceSuffix, markerWord, d0, d1,
      d1pow, sideBit, m0EvenEightBridgeStart]

/-- The valuation-dependent run of ones begins exactly at source offset 14. -/
private theorem sourceSuffix_extraOnes (t len u i : Nat)
    (hi : i < 3*t) :
    sideBit (m0EvenEightValuationSourceSuffix t len u) (14+i) = true := by
  have hprefix : (markerWord 0 ++ d0).length = 5 := by
    simp [markerWord, d0]
  rw [m0EvenEightValuationSourceSuffix, sideBit_append_right
    (markerWord 0 ++ d0)
    (d1pow (3+t) ++ d0 ++ binDec len u ++ lh) (14+i) (by omega)]
  have hindex : 14+i-5 = 9+i := by omega
  rw [hindex]
  have hinside : 9+i < (d1pow (3+t)).length := by
    simp [d1pow_length]
    omega
  rw [sideBit_append_left (d1pow (3+t))
    (d0 ++ binDec len u ++ lh) (9+i) hinside]
  exact sideBit_d1pow_true (3+t) (9+i) (by omega)

/-- The first two cells after the valuation-dependent one-run are the
zero boundary consumed by the four-step exit. -/
private theorem sourceSuffix_zeroBoundary (t len u : Nat) :
    sideBit (m0EvenEightValuationSourceSuffix t len u) (14+3*t) = false ∧
    sideBit (m0EvenEightValuationSourceSuffix t len u) (15+3*t) = false := by
  have hprefix :
      (markerWord 0 ++ d0 ++ d1pow (3+t)).length = 14+3*t := by
    simp [markerWord, d0, d1pow_length]
    omega
  constructor
  · rw [m0EvenEightValuationSourceSuffix,
      sideBit_append_right (markerWord 0 ++ d0 ++ d1pow (3+t))
        (d0 ++ binDec len u ++ lh) (14+3*t) (by omega)]
    simp [d0, sideBit]
  · rw [m0EvenEightValuationSourceSuffix,
      sideBit_append_right (markerWord 0 ++ d0 ++ d1pow (3+t))
        (d0 ++ binDec len u ++ lh) (15+3*t) (by omega)]
    simp [d0, sideBit]

/-- The twelve fixed right-hand ones in the 44-step bridge output. -/
private theorem bridgeMid_twelve_ones (bit : Bool) (i : Nat)
    (hi : i < 12) :
    decide ((-12+(i:Int)) ∈ (bridgeMidWithBit bit).marked) = true := by
  have hcases :
      i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨
      i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h
    <;> subst i
    <;> simp [bridgeMidWithBit]

/-- The rightward 111-to-001 sweep leaves every cell at or beyond its
final head unchanged. -/
private theorem sweptRight1_preserves_right (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h+3*(n:Int) ≤ x) :
    sweptRight1 n T h x = T x := by
  induction n generalizing T h x with
  | zero =>
      simp [sweptRight1]
  | succ n ih =>
      simp only [sweptRight1]
      have hx' : (h+3)+3*(n:Int) ≤ x := by omega
      rw [ih (afterRight1 T h) (h+3) x hx']
      have hx0 : x ≠ h := by omega
      have hx1 : x ≠ h+1 := by omega
      have hx2 : x ≠ h+2 := by omega
      simp [afterRight1, hx0, hx1, hx2]

/-- The fixed 44-step bridge input agrees with the original source tape
on every cell it reads.  The boundary cell at relative position -14 is
deliberately not constrained: the bridge preserves it parametrically. -/
private theorem m0EvenEightValuationBridgeInputMatch
    (L q a b t len u : Nat) (h : Int)
    (ha : 0 < a)
    (hface :
      s1LeftFacing L (8*q) 0 a 0 =
        d1pow a ++ m0EvenEightValuationSourceSuffix t len u) :
    ∀ y, bridgeInside44 y = true →
      sweptLeft (3*a) (s1Config L (8*q) 0 a 0 b h).tape h
        (h-((3*a:Nat):Int)+y) =
      decide (y ∈ (bridgeStartWithBit (decide (0<t))).marked) := by
  intro y hy
  have hybounds : -13 ≤ y ∧ y ≤ 3 := by
    simpa [bridgeInside44] using hy
  by_cases hy0 : y ≤ 0
  · let i : Nat := Int.toNat (-y)
    have hiCast : (i:Int) = -y := by
      simp [i]
      omega
    have hi : i ≤ 13 := by omega
    have hcoord :
        h-((3*a:Nat):Int)+y = h-((3*a+i:Nat):Int) := by
      rw [hiCast]
      push_cast
      omega
    have hpres := sweptLeft_preserves_left (3*a)
      (s1Config L (8*q) 0 a 0 b h).tape h
      (h-((3*a:Nat):Int)+y) (by omega)
    have hcell := s1Config_left_cell L (8*q) 0 a 0 b h (3*a+i)
    rw [hface] at hcell
    rw [sideBit_d1pow_append a (3*a+i)
      (m0EvenEightValuationSourceSuffix t len u)
      (by simp [d1pow_length]; omega)] at hcell
    have hsource := sourceSuffix_prefix14_match t len u i hi
    have hmark :
        decide (y ∈ (bridgeStartWithBit (decide (0<t))).marked) =
          decide ((-(i:Int)) ∈ m0EvenEightBridgeStart.marked) := by
      have hyEq : y = -(i:Int) := by omega
      rw [hyEq]
      have hneq : (-(i:Int)) ≠ -14 := by omega
      simp [bridgeStartWithBit, hneq]
    calc
      sweptLeft (3*a) (s1Config L (8*q) 0 a 0 b h).tape h
          (h-((3*a:Nat):Int)+y)
        = (s1Config L (8*q) 0 a 0 b h).tape
            (h-((3*a:Nat):Int)+y) := hpres
      _ = sideBit (m0EvenEightValuationSourceSuffix t len u) i := by
        rw [hcoord]
        exact hcell
      _ = decide ((-(i:Int)) ∈ m0EvenEightBridgeStart.marked) := hsource
      _ = decide (y ∈ (bridgeStartWithBit (decide (0<t))).marked) := hmark.symm
  · have hypos : y=1 ∨ y=2 ∨ y=3 := by omega
    rcases hypos with rfl | rfl | rfl
    · have heq : h-((3*a:Nat):Int)+1 =
        h-((3*a-1:Nat):Int) := by omega
      rw [heq]
      have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config L (8*q) 0 a 0 b h).tape h
      simpa [bridgeStartWithBit, m0EvenEightBridgeStart] using hleft
    · have heq : h-((3*a:Nat):Int)+2 =
        h-((3*a-2:Nat):Int) := by omega
      rw [heq]
      have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config L (8*q) 0 a 0 b h).tape h (by omega)
      simpa [bridgeStartWithBit, m0EvenEightBridgeStart] using hblock
    · have heq : h-((3*a:Nat):Int)+3 =
        h-((3*a-3:Nat):Int) := by omega
      rw [heq]
      have hblock := sweptLeft_block (3*a) (3*a-3)
        (s1Config L (8*q) 0 a 0 b h).tape h (by omega)
      simpa [bridgeStartWithBit, m0EvenEightBridgeStart] using hblock

/-- The all-valuation marker-0 8q q4 cut tape, after the 9a sweep,
44-step fixed bridge, 9t zero-bubble sweep, four-step exit, and
3(4+t)-step state-1 right scan. -/
def m0EvenEightValuationQ4CutTape
    (L q a b t : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let T1 := sweptLeft (3*a) T h
  let hN := h-((3*a:Nat):Int)
  let bit := decide (0<t)
  let T2 := (frameAt T1 hN bridgeInside44
    (bridgeMidWithBit bit)).tape
  let hH := hN-14
  let T3 := sweptLeft (3*t) T2 hH
  let hB := hH-((3*t:Nat):Int)
  let T4 := afterZeroExit4 T3 hB
  let hR := hB+2
  let T5 := sweptRight1 (4+t) T4 hR
  after101 T5 hN

/-- Exact all-valuation q4 prefix with its source-word factorization exposed.
The explicit left-facing equality lets the later q4 suffix use the same
2-adic valuation witness. -/
theorem m0EvenEight_valuation_q4_prefix_run_of_leftFacing
    (L q a b u t len : Nat) (h : Int)
    (hL : 4 ≤ L) (hq : 0 < q)
    (hbound : 8*q < 2^L) (ha : 0 < a)
    (hface :
      s1LeftFacing L (8*q) 0 a 0 =
        d1pow a ++ m0EvenEightValuationSourceSuffix t len u) :
    run tm2 (60+12*a+12*t)
      (s1Config L (8*q) 0 a 0 b h) =
      some ⟨4,h,m0EvenEightValuationQ4CutTape L q a b t h⟩ := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N : Nat := 3*a
  let hN : Int := h-((N:Nat):Int)
  let bit : Bool := decide (0<t)
  let T1 := sweptLeft N T h
  let T2 := (frameAt T1 hN bridgeInside44
    (bridgeMidWithBit bit)).tape
  let hH : Int := hN-14
  let T3 := sweptLeft (3*t) T2 hH
  let hB : Int := hH-((3*t:Nat):Int)
  let T4 := afterZeroExit4 T3 hB
  let hR : Int := hB+2
  let T5 := sweptRight1 (4+t) T4 hR
  let T6 := after101 T5 hN
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell L (8*q) 0 a 0 b h i
    rw [hface] at hcell
    rw [sideBit_d1pow_append a i
      (m0EvenEightValuationSourceSuffix t len u)
      (by simp [d1pow_length]; omega)] at hcell
    have hside : sideBit (d1pow a ++
        m0EvenEightValuationSourceSuffix t len u) i = true := by
      rw [sideBit_append_left (d1pow a)
        (m0EvenEightValuationSourceSuffix t len u) i
        (by simp [d1pow_length]; omega)]
      exact sideBit_d1pow_true a i (by omega)
    simpa [T,hside] using hcell
  have hright0 : T (h+1) = false := by
    have hc := s1Config_right_cell L (8*q) 0 a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
  have hSweep :
      run tm2 (3*N) (s1Config L (8*q) 0 a 0 b h) =
        some ⟨3,hN,T1⟩ := by
    simpa [T,N,hN,T1] using counted_left_sweep N T h hOn hright0
  have hmatch := m0EvenEightValuationBridgeInputMatch
    L q a b t len u h ha hface
  have hBridge :=
    bridge_prefix44_at T1 hN bit hmatch
  have hrightBubble : T2 (hH+1) = false := by
    have hin : bridgeInside44 ((hH+1)-hN) = true := by
      simp [bridgeInside44,hH]
    have hf := frameAt_tape_inside T1 hN bridgeInside44
      (bridgeMidWithBit bit) (hH+1) hin
    have hm :
        decide ((hH+1-hN) ∈ (bridgeMidWithBit bit).marked) = false := by
      simp [hH,bridgeMidWithBit]
    simpa [T2] using hf.trans hm
  have hleftBubble : leftOnes T2 hH (3*t) := by
    intro i hi
    have hout : bridgeInside44 ((hH-(i:Int))-hN) = false := by
      simp [bridgeInside44,hH]
      omega
    have hf := frameAt_tape_outside T1 hN bridgeInside44
      (bridgeMidWithBit bit) (hH-(i:Int)) hout
    have hp := sweptLeft_preserves_left N T h
      (hH-(i:Int)) (by dsimp [hH,hN,N]; omega)
    have hcell := s1Config_left_cell L (8*q) 0 a 0 b h (3*a+14+i)
    rw [hface] at hcell
    rw [sideBit_d1pow_append a (3*a+14+i)
      (m0EvenEightValuationSourceSuffix t len u)
      (by simp [d1pow_length]; omega)] at hcell
    have hsource := sourceSuffix_extraOnes t len u i hi
    have hcoord :
        hH-(i:Int) = h-((3*a+14+i:Nat):Int) := by
      dsimp [hH,hN,N]
      omega
    calc
      T2 (hH-(i:Int)) = T1 (hH-(i:Int)) := by
        simpa [T2] using hf
      _ = T (hH-(i:Int)) := hp
      _ = sideBit (m0EvenEightValuationSourceSuffix t len u) (14+i) := by
        rw [hcoord]
        exact hcell
      _ = true := hsource
  have hleftZero : T2 (hB-1) = false := by
    have hout : bridgeInside44 ((hB-1)-hN) = false := by
      simp [bridgeInside44,hB,hH]
      omega
    have hf := frameAt_tape_outside T1 hN bridgeInside44
      (bridgeMidWithBit bit) (hB-1) hout
    have hp := sweptLeft_preserves_left N T h (hB-1)
      (by dsimp [hB,hH,hN,N]; omega)
    have hcell := s1Config_left_cell L (8*q) 0 a 0 b h (3*a+15+3*t)
    rw [hface] at hcell
    rw [sideBit_d1pow_append a (3*a+15+3*t)
      (m0EvenEightValuationSourceSuffix t len u)
      (by simp [d1pow_length]; omega)] at hcell
    have hsource := (sourceSuffix_zeroBoundary t len u).2
    have hcoord : hB-1 = h-((3*a+15+3*t:Nat):Int) := by
      dsimp [hB,hH,hN,N]
      omega
    calc
      T2 (hB-1) = T1 (hB-1) := by simpa [T2] using hf
      _ = T (hB-1) := hp
      _ = sideBit (m0EvenEightValuationSourceSuffix t len u) (15+3*t) := by
        rw [hcoord]
        exact hcell
      _ = false := hsource
  have hzero : T2 hB = false := by
    have hout : bridgeInside44 (hB-hN) = false := by
      simp [bridgeInside44,hB,hH]
      omega
    have hf := frameAt_tape_outside T1 hN bridgeInside44
      (bridgeMidWithBit bit) hB hout
    have hp := sweptLeft_preserves_left N T h hB
      (by dsimp [hB,hH,hN,N]; omega)
    have hcell := s1Config_left_cell L (8*q) 0 a 0 b h (3*a+14+3*t)
    rw [hface] at hcell
    rw [sideBit_d1pow_append a (3*a+14+3*t)
      (m0EvenEightValuationSourceSuffix t len u)
      (by simp [d1pow_length]; omega)] at hcell
    have hsource := (sourceSuffix_zeroBoundary t len u).1
    have hcoord : hB = h-((3*a+14+3*t:Nat):Int) := by
      dsimp [hB,hH,hN,N]
      omega
    calc
      T2 hB = T1 hB := by simpa [T2] using hf
      _ = T hB := hp
      _ = sideBit (m0EvenEightValuationSourceSuffix t len u) (14+3*t) := by
        rw [hcoord]
        exact hcell
      _ = false := hsource
  have hzeroBoundary := sweptLeft_zeroBoundary t T2 hH
    hleftZero hzero hrightBubble
  have hBubble :
      run tm2 (3*(3*t)) ⟨3,hH,T2⟩ =
        some ⟨3,hB,T3⟩ := by
    simpa [T3,hB,hH] using
      counted_left_sweep (3*t) T2 hH hleftBubble hrightBubble
  have hExit :=
    state3_zero_exit4 T3 hB
      hzeroBoundary.1 hzeroBoundary.2.1 hzeroBoundary.2.2
  have hfixed : ∀ i : Nat, i<12 → T2 (hH+2+(i:Int)) = true := by
    intro i hi
    have hin : bridgeInside44 ((hH+2+(i:Int))-hN) = true := by
      simp [bridgeInside44,hH]
      omega
    have hf := frameAt_tape_inside T1 hN bridgeInside44
      (bridgeMidWithBit bit) (hH+2+(i:Int)) hin
    have hm := bridgeMid_twelve_ones bit i hi
    simpa [T2,hH] using hf.trans hm
  have hrightOnes : rightOnes T4 hR (4+t) := by
    intro i hi
    obtain ⟨h0,h1,h2⟩ :=
      sweptLeft_creates_rightOnes t T2 hH hfixed i hi
    have hx0 : hR+3*(i:Int) ≠ hB-1 := by dsimp [hR]; omega
    have hx1 : hR+3*(i:Int)+1 ≠ hB-1 := by dsimp [hR]; omega
    have hx2 : hR+3*(i:Int)+2 ≠ hB-1 := by dsimp [hR]; omega
    have hy0 : hR+3*(i:Int) ≠ hB := by dsimp [hR]; omega
    have hy1 : hR+3*(i:Int)+1 ≠ hB := by dsimp [hR]; omega
    have hy2 : hR+3*(i:Int)+2 ≠ hB := by dsimp [hR]; omega
    have hz0 : hR+3*(i:Int) ≠ hB+1 := by dsimp [hR]; omega
    have hz1 : hR+3*(i:Int)+1 ≠ hB+1 := by dsimp [hR]; omega
    have hz2 : hR+3*(i:Int)+2 ≠ hB+1 := by dsimp [hR]; omega
    constructor
    · simpa [T4,afterZeroExit4,hx0,hy0,hz0] using h0
    constructor
    · simpa [T4,afterZeroExit4,hx1,hy1,hz1] using h1
    · simpa [T4,afterZeroExit4,hx2,hy2,hz2] using h2
  have hScan0 := counted_right_sweep_from1 (4+t) T4 hR hrightOnes
  have hscanHead : hR+3*((4+t):Int) = hN := by
    dsimp [hR,hB,hH,hN,N]
    omega
  have hScan :
      run tm2 (3*(4+t)) ⟨1,hR,T4⟩ =
        some ⟨1,hN,T5⟩ := by
    simpa [T5,hscanHead] using hScan0
  have hT2zero : T2 hN = true := by
    have hin : bridgeInside44 (hN-hN) = true := by simp [bridgeInside44]
    have hf := frameAt_tape_inside T1 hN bridgeInside44
      (bridgeMidWithBit bit) hN hin
    have hm : decide (0 ∈ (bridgeMidWithBit bit).marked) = true := by
      simp [bridgeMidWithBit]
    simpa [T2] using hf.trans hm
  have hT2one : T2 (hN+1) = false := by
    have hin : bridgeInside44 ((hN+1)-hN) = true := by simp [bridgeInside44]
    have hf := frameAt_tape_inside T1 hN bridgeInside44
      (bridgeMidWithBit bit) (hN+1) hin
    have hm : decide (1 ∈ (bridgeMidWithBit bit).marked) = false := by
      simp [bridgeMidWithBit]
    simpa [T2] using hf.trans hm
  have hT2two : T2 (hN+2) = true := by
    have hin : bridgeInside44 ((hN+2)-hN) = true := by simp [bridgeInside44]
    have hf := frameAt_tape_inside T1 hN bridgeInside44
      (bridgeMidWithBit bit) (hN+2) hin
    have hm : decide (2 ∈ (bridgeMidWithBit bit).marked) = true := by
      simp [bridgeMidWithBit]
    simpa [T2] using hf.trans hm
  have hT3zero : T3 hN = T2 hN := by
    exact sweptLeft_preserves_right (3*t) T2 hH hN (by dsimp [hH]; omega)
  have hT3one : T3 (hN+1) = T2 (hN+1) := by
    exact sweptLeft_preserves_right (3*t) T2 hH (hN+1) (by dsimp [hH]; omega)
  have hT3two : T3 (hN+2) = T2 (hN+2) := by
    exact sweptLeft_preserves_right (3*t) T2 hH (hN+2) (by dsimp [hH]; omega)
  have hT4zero : T4 hN = T3 hN := by
    simp [T4,afterZeroExit4]
    all_goals dsimp [hB,hH,hN,N] at * <;> omega
  have hT4one : T4 (hN+1) = T3 (hN+1) := by
    simp [T4,afterZeroExit4]
    all_goals dsimp [hB,hH,hN,N] at * <;> omega
  have hT4two : T4 (hN+2) = T3 (hN+2) := by
    simp [T4,afterZeroExit4]
    all_goals dsimp [hB,hH,hN,N] at * <;> omega
  have hT5zero : T5 hN = T4 hN := by
    dsimp [T5]
    exact sweptRight1_preserves_right (4+t) T4 hR hN (by rw [hscanHead])
  have hT5one : T5 (hN+1) = T4 (hN+1) := by
    dsimp [T5]
    exact sweptRight1_preserves_right (4+t) T4 hR (hN+1) (by rw [hscanHead]; omega)
  have hT5two : T5 (hN+2) = T4 (hN+2) := by
    dsimp [T5]
    exact sweptRight1_preserves_right (4+t) T4 hR (hN+2) (by rw [hscanHead]; omega)
  have hBoundary :=
    state1_101_boundary T5 hN
      (by rw [hT5zero,hT4zero,hT3zero,hT2zero])
      (by rw [hT5one,hT4one,hT3one,hT2one])
      (by rw [hT5two,hT4two,hT3two,hT2two])
  have hLinear : linearRightOnes T6 (hN+3) (3*(a-1)) := by
    intro i hi
    by_cases hi0 : i=0
    · subst i
      have hin : bridgeInside44 ((hN+3)-hN) = true := by simp [bridgeInside44]
      have hf := frameAt_tape_inside T1 hN bridgeInside44
        (bridgeMidWithBit bit) (hN+3) hin
      have hm : decide (3 ∈ (bridgeMidWithBit bit).marked) = true := by
        simp [bridgeMidWithBit]
      have hT2 : T2 (hN+3) = true := by
        simpa [T2] using hf.trans hm
      have hT3 : T3 (hN+3) = T2 (hN+3) :=
        sweptLeft_preserves_right (3*t) T2 hH (hN+3) (by dsimp [hH]; omega)
      have hT4 : T4 (hN+3) = T3 (hN+3) := by
        simp [T4,afterZeroExit4]
        all_goals dsimp [hB,hH,hN,N] at * <;> omega
      have hT5 : T5 (hN+3) = T4 (hN+3) := by
        dsimp [T5]
        exact sweptRight1_preserves_right (4+t) T4 hR (hN+3)
          (by rw [hscanHead]; omega)
      have hT6 : T6 (hN+3) = T5 (hN+3) := by
        simp [T6,after101]
      rw [hT6,hT5,hT4,hT3,hT2]
    · have hpos : 0 < i := by omega
      let x : Int := hN+3+(i:Int)
      have hout : bridgeInside44 (x-hN) = false := by
        simp [bridgeInside44,x]
        omega
      have hf := frameAt_tape_outside T1 hN bridgeInside44
        (bridgeMidWithBit bit) x hout
      have hT2 : T2 x = T1 x := by simpa [T2] using hf
      have hT3 : T3 x = T2 x :=
        sweptLeft_preserves_right (3*t) T2 hH x (by dsimp [hH,x]; omega)
      have hT4 : T4 x = T3 x := by
        simp [T4,afterZeroExit4]
        all_goals dsimp [hB,hH,hN,N,x] at * <;> omega
      have hlast : hR+3*((4+t):Int) = hN := by
        dsimp [hR,hB,hH]
        omega
      have hT5 : T5 x = T4 x := by
        have hp := sweptRight1_preserves_right_local (4+t) T4 hR x (by
          rw [hscanHead]
          dsimp [x]
          omega)
        simpa [T5] using hp
      have hx0 : x ≠ hN := by dsimp [x]; omega
      have hx1 : x ≠ hN+1 := by dsimp [x]; omega
      have hx2 : x ≠ hN+2 := by dsimp [x]; omega
      have hT6 : T6 x = T5 x := by
        simp [T6,after101,hx0,hx1,hx2]
      let j : Nat := 3*a-3-i
      have hj : j+1 < N := by dsimp [j,N] at *; omega
      have hblock := sweptLeft_block N j T h hj
      have hcoord : x = h-(j:Int) := by
        dsimp [x,j,hN,N]
        omega
      have hT1 : T1 x = true := by
        change sweptLeft N T h x = true
        rw [hcoord]
        exact hblock
      rw [hT6,hT5,hT4,hT3,hT2,hT1]
  have hE := E_scan T6 (hN+3) (3*(a-1)) hLinear
  have hhead : hN+3+3*((a-1:Nat):Int) = h := by
    dsimp [hN,N]
    omega
  have hE' :
      run tm2 (3*(a-1)) ⟨4,hN+3,T6⟩ =
        some ⟨4,h,T6⟩ := by
    simpa [hhead] using hE
  have htotal :
      run tm2
        (3*N+44+3*(3*t)+4+3*(4+t)+3+3*(a-1))
        (s1Config L (8*q) 0 a 0 b h) =
      some ⟨4,h,T6⟩ := by
    simp only [Nat.add_assoc]
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge]
    simp only [Option.bind_some]
    have hBridgeConfig :
        frameAt T1 hN bridgeInside44 (bridgeMidWithBit bit) =
          (⟨3,hH,T2⟩ : Config) := by
      apply config_ext_local
      · rfl
      · dsimp [frameAt,bridgeMidWithBit,hH]
        omega
      · rfl
    rw [run_append,hBridgeConfig,hBubble]
    simp only [Option.bind_some]
    rw [run_append,hExit]
    simp only [Option.bind_some]
    rw [run_append,hScan]
    simp only [Option.bind_some]
    rw [run_append,hBoundary]
    simp only [Option.bind_some]
    exact hE'
  have hnum :
      3*N+44+3*(3*t)+4+3*(4+t)+3+3*(a-1) =
        60+12*a+12*t := by
    dsimp [N]
    omega
  simpa [m0EvenEightValuationQ4CutTape,T,N,hN,bit,T1,T2,hH,T3,hB,T4,hR,T5,T6,hnum]
    using htotal

/-- Existential convenience wrapper for the exact factorized prefix theorem. -/
theorem m0EvenEight_valuation_q4_prefix_run
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hq : 0 < q)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    ∃ t,
      run tm2 (60+12*a+12*t)
        (s1Config L (8*q) 0 a 0 b h) =
      some ⟨4,h,m0EvenEightValuationQ4CutTape L q a b t h⟩ := by
  obtain ⟨u,t,len,hfactor,hlen,hu,hface⟩ :=
    s1LeftFacing_8q_all L q a hL hq hbound
  exact ⟨t, m0EvenEight_valuation_q4_prefix_run_of_leftFacing
    L q a b u t len h hL hq hbound ha
    (by
      have hface' := hface
      rw [Nat.add_comm t 3] at hface'
      simpa [m0EvenEightValuationSourceSuffix] using hface')⟩

#print axioms sourceSuffix_prefix14_match
#print axioms sourceSuffix_extraOnes
#print axioms sourceSuffix_zeroBoundary
#print axioms m0EvenEightValuationBridgeInputMatch
#print axioms m0EvenEight_valuation_q4_prefix_run_of_leftFacing
#print axioms m0EvenEight_valuation_q4_prefix_run

end BB6Coverage.Agent48M0EvenEightValuationSource
