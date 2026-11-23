import M1OddQ4Bridge
import Q4RightEndpoint
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Source-level m=1, n=8q+5 odd q4 reset prefix

This is the next genuine TM63 middle-row successor after the
(m=0,n=16r+7) reset and the intervening (m=2,n=16r+6) decrement.
It uses the 26-step original-table bridge shared with Agent 42.

The theorem is parameterized over the actual S1 encoding, not a copied
machine.  The finite bridge window is [-6,1]; the source/target left
streams agree from index 3a+8 onward, and the two differing bits are
exactly the bridge's marks at -5 and -6.
-/

namespace BB6Coverage.Agent24M1ResidueFive

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42M1OddQ4Bridge
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48CountedInc0
open BB6ChampionArithmetic

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) :=
  Agent6Q4Prefix.sideBit_append_right xs ys i hi

private theorem pow2_mul_pow (n k c : Nat) (hc : 2^k = c) :
    2^(n+k) = c*2^n := by
  calc
    2^(n+k) = 2^n * 2^k := Nat.pow_add 2 n k
    _ = 2^n * c := by rw [hc]
    _ = c * 2^n := Nat.mul_comm _ _

/-- The low three blocks of the source binary word for n=8q+5. -/
theorem m1ResidueFive_binDec (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+5 < 2^L) :
    binDec L (8*q+5) =
      d0 ++ d1 ++ d0 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega]
    exact pow2_mul_pow (L-3) 3 8 (by decide)
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega]
    exact pow2_mul_pow (L-3) 2 4 (by decide)
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega]
    exact pow2_mul_pow (L-3) 1 2 (by decide)
  have hbound' : 8*q+5 < 8*2^(L-3) := by
    rw [← hpow3]
    exact hbound
  have hq1 : 4*q+2 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*q+1 < 2^(L-2) := by
    rw [hpow1]
    omega
  have hq : q < 2^(L-3) := by
    omega
  have h1 : binDec L (8*q+5) =
      d0 ++ binDec (L-1) (4*q+2) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q+5 = 2*(4*q+2)+1 by omega]
    exact binDec_odd (L-1) (4*q+2) hq1
  have h2 : binDec (L-1) (4*q+2) =
      d1 ++ binDec (L-2) (2*q+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q+2 = 2*(2*q+1) by omega]
    exact binDec_even (L-2) (2*q+1) hq2
  have h3 : binDec (L-2) (2*q+1) =
      d0 ++ binDec (L-3) q := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) q hq
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- The low three blocks of the target binary word for n-1=8q+4. -/
theorem m1ResidueFour_binDec (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+5 < 2^L) :
    binDec L (8*q+4) =
      d1 ++ d1 ++ d0 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega]
    exact pow2_mul_pow (L-3) 3 8 (by decide)
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega]
    exact pow2_mul_pow (L-3) 2 4 (by decide)
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega]
    exact pow2_mul_pow (L-3) 1 2 (by decide)
  have hbound' : 8*q+5 < 8*2^(L-3) := by
    rw [← hpow3]
    exact hbound
  have hq1 : 4*q+2 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*q+1 < 2^(L-2) := by
    rw [hpow1]
    omega
  have hq : q < 2^(L-3) := by
    omega
  have h1 : binDec L (8*q+4) =
      d1 ++ binDec (L-1) (4*q+2) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q+4 = 2*(4*q+2) by omega]
    exact binDec_even (L-1) (4*q+2) hq1
  have h2 : binDec (L-1) (4*q+2) =
      d1 ++ binDec (L-2) (2*q+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q+2 = 2*(2*q+1) by omega]
    exact binDec_even (L-2) (2*q+1) hq2
  have h3 : binDec (L-2) (2*q+1) =
      d0 ++ binDec (L-3) q := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) q hq
  rw [h1,h2,h3]
  simp [List.append_assoc]

private def m1ResidueFiveSourceSuffix (L q : Nat) : List Bool :=
  markerWord 1 ++ d0 ++ d0 ++ d1 ++ d0 ++ binDec (L-3) q ++ lh

private theorem m1ResidueFiveSourceLeftAt
    (L q a b : Nat) (h : Int) (k : Nat)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) :
    (s1Config L (8*q+5) 1 a 0 b h).tape
      (h - ((3*a+1+k : Nat) : Int)) =
      sideBit (m1ResidueFiveSourceSuffix L q) (1+k) := by
  have hleft :
      s1LeftFacing L (8*q+5) 1 a 0 =
        d1pow a ++ m1ResidueFiveSourceSuffix L q := by
    simp [s1LeftFacing,binDec_zero,m1ResidueFiveSourceSuffix,
      m1ResidueFive_binDec L q hL hbound,List.append_assoc]
  have hcell := s1Config_left_cell L (8*q+5) 1 a 0 b h (3*a+1+k)
  have hside := sideBit_d1pow_append a (3*a+1+k)
    (m1ResidueFiveSourceSuffix L q) (by omega)
  rw [hleft] at hcell
  rw [hside] at hcell
  simpa only [show 3*a+1+k-3*a = 1+k by omega] using hcell

private theorem m1ResidueFiveSweptLeftCell
    (L q a b : Nat) (h : Int) (k : Nat)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) :
    sweptLeft (3*a+1)
      (s1Config L (8*q+5) 1 a 0 b h).tape h
      (h - ((3*a+1 : Nat) : Int) - (k : Int)) =
      sideBit (m1ResidueFiveSourceSuffix L q) (1+k) := by
  have hpres := sweptLeft_preserves_left (3*a+1)
    (s1Config L (8*q+5) 1 a 0 b h).tape h
    (h - ((3*a+1 : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m1ResidueFiveSourceLeftAt L q a b h k hL hbound
  have hcoord :
      h - ((3*a+1 : Nat) : Int) - (k : Int) =
        h - ((3*a+1+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- The complete [-6,1] input window of the 26-step bridge is produced
by the counted left sweep from the authentic S1 source. -/
theorem m1ResidueFiveBridge_input_match
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    ∀ y, m1OddQ4BridgeInside y = true →
      (sweptLeft (3*a+1)
        (s1Config L (8*q+5) 1 a 0 b h).tape h)
        (h - ((3*a+1 : Nat) : Int) + y) =
          decide (y ∈ m1OddQ4BridgeStart.marked) := by
  intro y hy
  have hyb : -6 ≤ y ∧ y ≤ 1 := by
    simpa [m1OddQ4BridgeInside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a+1 : Nat) : Int) + y =
          h - ((3*a+1 : Nat) : Int) - (k : Int) := by
      rw [hkcast]
      omega
    rw [hcoord]
    have hleft := m1ResidueFiveSweptLeftCell L q a b h k hL hbound
    have hbits :
        sideBit (m1ResidueFiveSourceSuffix L q) (1+k) =
          decide (y ∈ m1OddQ4BridgeStart.marked) := by
      have hyCases :
          y = -6 ∨ y = -5 ∨ y = -4 ∨ y = -3 ∨
          y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h6 | h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m1ResidueFiveSourceSuffix,
        markerWord,d0,d1,lh,sideBit,m1OddQ4BridgeStart]
    exact hleft.trans hbits
  · have hy1 : y = 1 := by omega
    subst y
    have hleft := sweptLeft_leftmost (3*a)
      (s1Config L (8*q+5) 1 a 0 b h).tape h
    have hcoord :
        h - ((3*a+1 : Nat) : Int) + 1 =
          h - ((3*a : Nat) : Int) := by omega
    rw [hcoord]
    simpa [m1OddQ4BridgeStart] using hleft

/-- Explicit tape at the m=1,n=8q+5 q4 cut. -/
def m1ResidueFiveQ4CutTape
    (L q a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config L (8*q+5) 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int))
    m1OddQ4BridgeInside m1OddQ4BridgeEnd).tape

private theorem m1ResidueFiveQ4CutTape_eq_swept
    (L q a b : Nat) (h x : Int)
    (hout : m1OddQ4BridgeInside
      (x-(h-((3*a+1 : Nat) : Int))) = false) :
    m1ResidueFiveQ4CutTape L q a b h x =
      sweptLeft (3*a+1)
        (s1Config L (8*q+5) 1 a 0 b h).tape h x := by
  have hcut := frameAt_tape_outside
    (sweptLeft (3*a+1)
      (s1Config L (8*q+5) 1 a 0 b h).tape h)
    (h-((3*a+1 : Nat):Int)) m1OddQ4BridgeInside
    m1OddQ4BridgeEnd x hout
  simpa [m1ResidueFiveQ4CutTape] using hcut

private theorem m1ResidueFiveQ4CutTape_eq_end_inside
    (L q a b : Nat) (h x : Int)
    (hin : m1OddQ4BridgeInside
      (x-(h-((3*a+1 : Nat) : Int))) = true) :
    m1ResidueFiveQ4CutTape L q a b h x =
      decide ((x-(h-((3*a+1 : Nat) : Int))) ∈
        m1OddQ4BridgeEnd.marked) := by
  have hcut := frameAt_tape_inside
    (sweptLeft (3*a+1)
      (s1Config L (8*q+5) 1 a 0 b h).tape h)
    (h-((3*a+1 : Nat):Int)) m1OddQ4BridgeInside
    m1OddQ4BridgeEnd x hin
  simpa [m1ResidueFiveQ4CutTape] using hcut

/-- The source reset prefix: 28+12a primitive moves to state E at
the original head. -/
theorem m1ResidueFive_q4_prefix_run
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    run tm2 (28+12*a)
      (s1Config L (8*q+5) 1 a 0 b h) =
      some ⟨4,h,m1ResidueFiveQ4CutTape L q a b h⟩ := by
  let T := (s1Config L (8*q+5) 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m1ResidueFiveQ4CutTape L q a b h
  have hleftFacing :
      s1LeftFacing L (8*q+5) 1 a 0 =
        d1pow a ++ m1ResidueFiveSourceSuffix L q := by
    simp [s1LeftFacing,binDec_zero,m1ResidueFiveSourceSuffix,
      m1ResidueFive_binDec L q hL hbound,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell L (8*q+5) 1 a 0 b h i
    have hside : sideBit (s1LeftFacing L (8*q+5) 1 a 0) i = true := by
      rw [hleftFacing]
      by_cases hi3 : i < 3*a
      · have hiLen : i < (d1pow a).length := by
          simpa [d1pow_length] using hi3
        rw [Agent6Q4Prefix.sideBit_append_left
          (d1pow a) (m1ResidueFiveSourceSuffix L q) i hiLen]
        exact sideBit_d1pow_true a i hi3
      · have hieq : i = 3*a := by omega
        subst i
        have hlen : (d1pow a).length = 3*a := by
          simp [d1pow_length]
        rw [sideBit_append_right (d1pow a)
          (m1ResidueFiveSourceSuffix L q) (3*a) (by simpa [hlen])]
        simp [m1ResidueFiveSourceSuffix,markerWord,d0,d1,sideBit,d1pow_length]
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell L (8*q+5) 1 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m1ResidueFiveBridge_input_match L q a b h hL hbound ha
  have hBridge := bridgeAt T1 hN m1OddQ4BridgeInside
    m1OddQ4BridgeStart m1OddQ4BridgeEnd 26 rfl
    m1OddQ4Bridge_exact m1OddQ4Bridge_heads hmatch
  have hBridge' :
      run tm2 26 ⟨3,hN,T1⟩ = some ⟨4,hN+2,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m1OddQ4BridgeInside m1OddQ4BridgeEnd =
          (⟨4,hN+2,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m1OddQ4BridgeEnd]
      · simp [frameAt_head,m1OddQ4BridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+2) (3*a-1) := by
    intro i hi
    let x : Int := hN+2+(i:Int)
    have hout : m1OddQ4BridgeInside (x-hN) = false := by
      simp [m1OddQ4BridgeInside,x]
      omega
    have hcut := Agent6Q4Prefix.frameAt_tape_outside T1 hN
      m1OddQ4BridgeInside m1OddQ4BridgeEnd x hout
    have hframe : T2 x = T1 x := by
      simpa [T2,m1ResidueFiveQ4CutTape] using hcut
    let j : Nat := 3*a-1-i
    have hj : j+1 < N := by
      dsimp [j,N]
      omega
    have hblock := sweptLeft_block N j T h hj
    have hcoord : x = h-(j:Int) := by
      dsimp [x,j,hN,N]
      omega
    have hT1 : T1 x = true := by
      rw [hcoord]
      exact hblock
    exact hframe.trans hT1
  have hScan := E_scan T2 (hN+2) (3*a-1) hlinear
  have hhead : hN+2+((3*a-1 : Nat):Int) = h := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*a-1) ⟨4,hN+2,T2⟩ = some ⟨4,h,T2⟩ := by
    rw [hhead] at hScan
    exact hScan
  have hSweep' :
      run tm2 (3*N) ⟨3,h,T⟩ = some ⟨3,hN,T1⟩ := by
    simpa [N,hN,T1] using hSweep
  have htotal :
      run tm2 (3*N+(26+(3*a-1))) ⟨3,h,T⟩ =
        some ⟨4,h,T2⟩ := by
    rw [run_append,hSweep']
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 28+12*a = 3*N+(26+(3*a-1)) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m1ResidueFiveQ4CutTape,hnum,s1Config,s0Config] using htotal

private theorem sideBit_s0RightFacing_eq_q4RightFacing
    (b i : Nat) (hi : 1 ≤ i) :
    sideBit (s0RightFacing b) i = sideBit (q4RightFacing b) i := by
  by_cases hi6 : i < 6
  · have hcases : i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
    rcases hcases with h1 | h2 | h3 | h4 | h5
    all_goals subst i
    all_goals simp [s0RightFacing,q4RightFacing,sideBit]
  · have hs := sideBit_append_after_local
      [false,true,true,true,false,false] (d1pow (b+1)) i
      (by simp; omega)
    have ht := sideBit_append_after_local
      [true,true,true,true,false,false] (d1pow (b+1)) i
      (by simp; omega)
    simpa [s0RightFacing,q4RightFacing] using hs.trans ht.symm

/-- The right-facing stream at the new cut is the generic q4 word. -/
theorem m1ResidueFive_q4_prefix_rightFacing
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    ∀ i : Nat,
      m1ResidueFiveQ4CutTape L q a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i := by
  intro i
  by_cases hi0 : i=0
  · subst i
    have hout : m1OddQ4BridgeInside
        ((h+1)-(h-((3*a+1 : Nat):Int))) = false := by
      simp [m1OddQ4BridgeInside]
      omega
    have hcut := m1ResidueFiveQ4CutTape_eq_swept
      L q a b h (h+1) hout
    have hplus := sweptLeft_plus1 (3*a)
      (s1Config L (8*q+5) 1 a 0 b h).tape h
    have hN : (3*a)+1 = 3*a+1 := by omega
    rw [hN] at hplus
    have hval :
        m1ResidueFiveQ4CutTape L q a b h (h+1) = true := by
      exact hcut.trans hplus
    simpa [q4RightFacing,sideBit] using hval
  · have hi : 1 ≤ i := by omega
    have hout : m1OddQ4BridgeInside
        ((h+1+(i:Int))-(h-((3*a+1 : Nat):Int))) = false := by
      simp [m1OddQ4BridgeInside]
      omega
    have hcut := m1ResidueFiveQ4CutTape_eq_swept
      L q a b h (h+1+(i:Int)) hout
    have hpres := sweptLeft_preserves_right (3*a+1)
      (s1Config L (8*q+5) 1 a 0 b h).tape h
      (h+1+(i:Int)) (by omega)
    have hsrc :
        (s1Config L (8*q+5) 1 a 0 b h).tape
          (h+1+(i:Int)) = sideBit (s0RightFacing b) i := by
      simpa [s0RightFacing,s1PhysicalRight_source,sideBit] using
        s1Config_right_cell L (8*q+5) 1 a 0 b h i
    have hside := sideBit_s0RightFacing_eq_q4RightFacing b i hi
    calc
      m1ResidueFiveQ4CutTape L q a b h (h+1+(i:Int)) =
          sweptLeft (3*a+1)
            (s1Config L (8*q+5) 1 a 0 b h).tape h
            (h+1+(i:Int)) := hcut
      _ = (s1Config L (8*q+5) 1 a 0 b h).tape
            (h+1+(i:Int)) := hpres
      _ = sideBit (s0RightFacing b) i := hsrc
      _ = sideBit (q4RightFacing b) i := hside

private theorem sideBit_false_after_length_local
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih i hi'

/-- The infinite blank right tail required by the generic q4 suffix. -/
theorem m1ResidueFive_q4_prefix_far_tail
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m1ResidueFiveQ4CutTape L q a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hr := m1ResidueFive_q4_prefix_rightFacing
    L q a b h hL hbound ha i
  have hlen : (q4RightFacing b).length = 9+3*b := by
    simp [q4RightFacing,d1pow_length] <;> omega
  have hblank := sideBit_false_after_length_local
    (q4RightFacing b) i (by omega)
  exact hr.trans hblank

/-- The exact left-facing target word at the m=1,n=8q+5 q4 cut. -/
def m1ResidueFiveQ4LeftFacing (L q a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L (8*q+4) ++ lh

private def m1ResidueFiveSourcePrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 1 ++ d0 ++ [false,false]

private def m1ResidueFiveTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ [true,true]

private def m1ResidueFiveCommonTail (L q : Nat) : List Bool :=
  [true] ++ d1 ++ d0 ++ binDec (L-3) q ++ lh

private theorem m1ResidueFiveLeftFacingPrefixTrue
    (L q a i : Nat) (hi : i ≤ 3*a) :
    sideBit (m1ResidueFiveQ4LeftFacing L q a) i = true := by
  have hlist :
      m1ResidueFiveQ4LeftFacing L q a =
        [true] ++ (d1pow a ++
          (markerWord 0 ++ d0 ++ binDec L (8*q+4) ++ lh)) := by
    simp [m1ResidueFiveQ4LeftFacing,List.append_assoc]
  by_cases hi0 : i = 0
  · subst i
    simp [hlist,sideBit]
  · have hpos : 1 ≤ i := by omega
    rw [hlist]
    rw [sideBit_append_after_local [true]
      (d1pow a ++ (markerWord 0 ++ d0 ++ binDec L (8*q+4) ++ lh))
      i (by simp; omega)]
    change sideBit (d1pow a ++
      (markerWord 0 ++ d0 ++ binDec L (8*q+4) ++ lh)) (i-1) = true
    have hrest := sideBit_append_left (d1pow a)
      (markerWord 0 ++ d0 ++ binDec L (8*q+4) ++ lh) (i-1) (by
        have hi' : i-1 < 3*a := by omega
        simpa [d1pow_length] using hi')
    rw [hrest]
    exact sideBit_d1pow_true a (i-1) (by omega)

private theorem m1ResidueFiveLeftFacingTail
    (L q a i : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+5 < 2^L) (hi : 3*a+8 ≤ i) :
    sideBit (s1LeftFacing L (8*q+5) 1 a 0) i =
      sideBit (m1ResidueFiveQ4LeftFacing L q a) i := by
  have hsrc :
      s1LeftFacing L (8*q+5) 1 a 0 =
        m1ResidueFiveSourcePrefix a ++ m1ResidueFiveCommonTail L q := by
    simp [s1LeftFacing,binDec_zero,m1ResidueFiveSourcePrefix,
      m1ResidueFiveCommonTail,m1ResidueFive_binDec L q hL hbound,
      d0,d1,List.append_assoc]
  have htgt :
      m1ResidueFiveQ4LeftFacing L q a =
        m1ResidueFiveTargetPrefix a ++ m1ResidueFiveCommonTail L q := by
    simp [m1ResidueFiveQ4LeftFacing,m1ResidueFiveTargetPrefix,
      m1ResidueFiveCommonTail,m1ResidueFour_binDec L q hL hbound,
      d0,d1,List.append_assoc]
  have hlenS :
      (m1ResidueFiveSourcePrefix a).length = 3*a+8 := by
    simp [m1ResidueFiveSourcePrefix,d1pow_length,markerWord,d0]
  have hlenT :
      (m1ResidueFiveTargetPrefix a).length = 3*a+8 := by
    simp [m1ResidueFiveTargetPrefix,d1pow_length,markerWord,d0,d1]
  have hs := sideBit_append_after_local
    (m1ResidueFiveSourcePrefix a) (m1ResidueFiveCommonTail L q) i
    (by rw [hlenS]; omega)
  have ht := sideBit_append_after_local
    (m1ResidueFiveTargetPrefix a) (m1ResidueFiveCommonTail L q) i
    (by rw [hlenT]; omega)
  rw [hsrc,htgt,hs,ht]
  simp [hlenS,hlenT]

private theorem m1ResidueFiveQ4CutTape_eq_source_left
    (L q a b : Nat) (h : Int) (i : Nat)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L)
    (hi : 3*a+8 ≤ i) :
    m1ResidueFiveQ4CutTape L q a b h (h-(i:Int)) =
      sideBit (s1LeftFacing L (8*q+5) 1 a 0) i := by
  have hout : m1OddQ4BridgeInside
      ((h-(i:Int))-(h-((3*a+1 : Nat):Int))) = false := by
    simp [m1OddQ4BridgeInside]
    omega
  have hcut := m1ResidueFiveQ4CutTape_eq_swept
    L q a b h (h-(i:Int)) hout
  have hpres := sweptLeft_preserves_left (3*a+1)
    (s1Config L (8*q+5) 1 a 0 b h).tape h
    (h-(i:Int)) (by omega)
  have hcell := s1Config_left_cell L (8*q+5) 1 a 0 b h i
  simpa using hcut.trans (hpres.trans hcell)

private theorem m1ResidueFiveLeftFacingBoundaryBit
    (L q a j : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+5 < 2^L) (hj : j ≤ 6) :
    sideBit (m1ResidueFiveQ4LeftFacing L q a) (3*a+1+j) =
      decide (-(j:Int) ∈ m1OddQ4BridgeEnd.marked) := by
  have hlist :
      m1ResidueFiveQ4LeftFacing L q a =
        ([true] ++ d1pow a) ++
          (markerWord 0 ++ d0 ++ binDec L (8*q+4) ++ lh) := by
    simp [m1ResidueFiveQ4LeftFacing,List.append_assoc]
  rw [hlist]
  have hside := sideBit_append_after_local
    ([true] ++ d1pow a)
    (markerWord 0 ++ d0 ++ binDec L (8*q+4) ++ lh)
    (3*a+1+j) (by simp [d1pow_length])
  have hidx : (3*a+1+j) - (3*a+1) = j := by omega
  have hlen : ([true] ++ d1pow a).length = 3*a+1 := by simp [d1pow_length]
  rw [hlen] at hside
  rw [hidx] at hside
  rw [hside]
  rw [m1ResidueFour_binDec L q hL hbound] at hside
  have hjCases :
      j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hjCases with h0 | h1 | h2 | h3 | h4 | h5 | h6
  all_goals subst j
  all_goals
    simp [markerWord,d0,d1,sideBit,m1OddQ4BridgeEnd] at hside ⊢
    exact hside

/-- Every cell of the cut's left-facing stream is identified, including
the two bits changed by the 26-step bridge. -/
theorem m1ResidueFive_q4_prefix_leftFacing
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    ∀ i : Nat,
      m1ResidueFiveQ4CutTape L q a b h (h-(i:Int)) =
        sideBit (m1ResidueFiveQ4LeftFacing L q a) i := by
  intro i
  by_cases hprefix : i < 3*a
  · have htarget := m1ResidueFiveLeftFacingPrefixTrue L q a i (by omega)
    have hout : m1OddQ4BridgeInside
        ((h-(i:Int))-(h-((3*a+1 : Nat):Int))) = false := by
      simp [m1OddQ4BridgeInside]
      omega
    have hcut := m1ResidueFiveQ4CutTape_eq_swept
      L q a b h (h-(i:Int)) hout
    have hblock := sweptLeft_block (3*a+1) i
      (s1Config L (8*q+5) 1 a 0 b h).tape h (by omega)
    have hval :
        m1ResidueFiveQ4CutTape L q a b h (h-(i:Int)) = true := by
      calc
        m1ResidueFiveQ4CutTape L q a b h (h-(i:Int)) =
            sweptLeft (3*a+1)
              (s1Config L (8*q+5) 1 a 0 b h).tape h
              (h-(i:Int)) := hcut
        _ = true := by simpa using hblock
    exact hval.trans htarget.symm
  · by_cases hieq : i = 3*a
    · have htarget := m1ResidueFiveLeftFacingPrefixTrue L q a i (by omega)
      have hin : m1OddQ4BridgeInside
          ((h-(i:Int))-(h-((3*a+1 : Nat):Int))) = true := by
        simp [m1OddQ4BridgeInside]
        omega
      have hcut := m1ResidueFiveQ4CutTape_eq_end_inside
        L q a b h (h-(i:Int)) hin
      have hmark :
          decide (((h-(i:Int))-(h-((3*a+1 : Nat):Int))) ∈
            m1OddQ4BridgeEnd.marked) = true := by
        have hcoord :
            (h-(i:Int))-(h-((3*a+1 : Nat):Int)) = 1 := by omega
        rw [hcoord]
        simp [m1OddQ4BridgeEnd]
      have hval : m1ResidueFiveQ4CutTape L q a b h
          (h-(i:Int)) = true := hcut.trans hmark
      exact hval.trans htarget.symm
    · by_cases htail : 3*a+8 ≤ i
      · have hcut := m1ResidueFiveQ4CutTape_eq_source_left
          L q a b h i hL hbound htail
        exact hcut.trans
          (m1ResidueFiveLeftFacingTail L q a i hL hbound htail)
      · have hbounds : 3*a+1 ≤ i ∧ i ≤ 3*a+7 := by omega
        let j : Nat := i-(3*a+1)
        have hj : j ≤ 6 := by dsimp [j]; omega
        have hrel :
            (h-(i:Int))-(h-((3*a+1 : Nat):Int)) =
              -(j:Int) := by
          dsimp [j]
          omega
        have hin : m1OddQ4BridgeInside
            ((h-(i:Int))-(h-((3*a+1 : Nat):Int))) = true := by
          rw [hrel]
          simp [m1OddQ4BridgeInside]
          omega
        have hcut := m1ResidueFiveQ4CutTape_eq_end_inside
          L q a b h (h-(i:Int)) hin
        have htarget := m1ResidueFiveLeftFacingBoundaryBit
          L q a j hL hbound hj
        have hcut' :
            m1ResidueFiveQ4CutTape L q a b h (h-(i:Int)) =
              decide (-(j:Int) ∈ m1OddQ4BridgeEnd.marked) := by
          rw [hrel] at hcut
          exact hcut
        have hval := hcut'.trans htarget.symm
        have hidx : i = 3*a+1+j := by dsimp [j]; omega
        simpa only [hidx] using hval

/-- The q4 right-shape contract follows from the exact right stream. -/
theorem m1ResidueFive_q4_prefix_rightShape
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    Agent8Q4Suffix.q4RightShape (m1ResidueFiveQ4CutTape L q a b h) h b := by
  unfold Agent8Q4Suffix.q4RightShape
  constructor
  · intro i hi
    have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst i
      have hleft := m1ResidueFive_q4_prefix_leftFacing
        L q a b h hL hbound ha 0
      simpa [m1ResidueFiveQ4LeftFacing,sideBit] using hleft
    · subst i
      have hr := m1ResidueFive_q4_prefix_rightFacing
        L q a b h hL hbound ha 0
      simpa [q4RightFacing,sideBit] using hr
    · subst i
      have hr := m1ResidueFive_q4_prefix_rightFacing
        L q a b h hL hbound ha 1
      have hcoord : h+2 = h+1+(1:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
    · subst i
      have hr := m1ResidueFive_q4_prefix_rightFacing
        L q a b h hL hbound ha 2
      have hcoord : h+3 = h+1+(2:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
    · subst i
      have hr := m1ResidueFive_q4_prefix_rightFacing
        L q a b h hL hbound ha 3
      have hcoord : h+4 = h+1+(3:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
  · constructor
    · have hr := m1ResidueFive_q4_prefix_rightFacing
        L q a b h hL hbound ha 4
      have hcoord : h+5 = h+1+(4:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
    · constructor
      · have hr := m1ResidueFive_q4_prefix_rightFacing
          L q a b h hL hbound ha 5
        have hcoord : h+6 = h+1+(5:Int) := by omega
        simpa [hcoord,q4RightFacing,sideBit] using hr
      · constructor
        · intro i hi
          have hr := m1ResidueFive_q4_prefix_rightFacing
            L q a b h hL hbound ha (6+i)
          have hsplit := sideBit_append_after_local
            [true,true,true,true,false,false] (d1pow (b+1)) (6+i)
            (by simp)
          have hsplit' :
              sideBit ([true,true,true,true,false,false] ++ d1pow (b+1))
                  (6+i) =
                sideBit (d1pow (b+1)) ((6+i)-6) := by
            simpa using hsplit
          have hidx : (6+i)-6 = i := by omega
          have hones : sideBit (q4RightFacing b) (6+i) = true := by
            rw [q4RightFacing]
            rw [hidx] at hsplit'
            exact hsplit'.trans (sideBit_d1pow_true (b+1) i (by omega))
          have hcoord : h+7+(i:Int) = h+1+((6+i:Int)) := by omega
          simpa [hcoord] using hr.trans hones
        · intro i hi
          have hr := m1ResidueFive_q4_prefix_rightFacing
            L q a b h hL hbound ha (9+3*b+i)
          have hlen : (q4RightFacing b).length = 9+3*b := by
            simp [q4RightFacing,d1pow_length] <;> omega
          have hblank := sideBit_false_after_length_local
            (q4RightFacing b) (9+3*b+i) (by omega)
          have hcoord :
              h+10+(3*b:Int)+(i:Int) =
                h+1+((9+3*b+i:Int)) := by omega
          simpa [hcoord] using hr.trans hblank


/-- The generic q4 suffix sees exactly the next S1 left-facing word. -/
theorem m1ResidueFiveQ4SuffixTargetLeft
    (L q a b : Nat) :
    s1LeftFacing L (8*q+4) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1ResidueFiveQ4LeftFacing L q a).drop 1 := by
  unfold s1LeftFacing m1ResidueFiveQ4LeftFacing
  rw [binDec_pow2_sub_one]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc]

theorem m1ResidueFive_resetPrefixCost_eq (q a b : Nat) :
    resetPrefixCost 1 (8*q+5) a b = 67+12*a+3*b := by
  have hv : BB6ChampionArithmetic.v2 (8*q+5) = 0 :=
    v2_of_odd (8*q+5) (by omega)
  simp [resetPrefixCost,hv]
  omega

/-- Complete original-table source reset prefix for every n=8q+5. -/
theorem m1ResidueFive_reset_prefix_to_s1
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    run tm2 (resetPrefixCost 1 (8*q+5) a b)
      (s1Config L (8*q+5) 1 a 0 b h) =
      some (s1Config L (8*q+4) 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m1ResidueFiveQ4CutTape L q a b h
  have hprefix := m1ResidueFive_q4_prefix_run L q a b h hL hbound ha
  have hshape := m1ResidueFive_q4_prefix_rightShape
    L q a b h hL hbound ha
  have htail := m1ResidueFive_q4_prefix_far_tail
    L q a b h hL hbound ha
  have hleft := m1ResidueFive_q4_prefix_leftFacing
    L q a b h hL hbound ha
  have happend := m1ResidueFiveQ4SuffixTargetLeft L q a b
  have hsuffix := q4_suffix_run_to_s1Config
    T h b L (8*q+4) 0 (a+b+2) (2^b-1)
    (m1ResidueFiveQ4LeftFacing L q a) hshape htail hleft happend
  have hsum :
      resetPrefixCost 1 (8*q+5) a b = (28+12*a)+(39+3*b) := by
    rw [m1ResidueFive_resetPrefixCost_eq]
    omega
  rw [hsum,run_append,hprefix]
  simpa using hsuffix

/-- Attach the authentic S1 counted drain to the residue-five prefix. -/
theorem m1ResidueFive_counted_increment_source
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 (8*q+5) a b)
      (s1Config L (8*q+5) 1 a 0 b h) =
      some (s1Config L (8*q+4) 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m1ResidueFive_reset_prefix_to_s1
    L q a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*q+4) 0 (a+b+2) b (h+5+3*b)
    (s1Config L (8*q+5) 1 a 0 b h)
    (resetPrefixCost 1 (8*q+5) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

private theorem m1ResidueFiveNextExponent_one_eq (a b : Nat) :
    nextExponent 1 a b = a+b+2 := rfl

private theorem m1ResidueFiveNextRight_eq (b : Nat) :
    nextRight b = 2^b-1 := rfl

/-- Symbolic successor form for direct use in the root countdown. -/
theorem m1ResidueFive_counted_increment_source_symbolic
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+5 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 (8*q+5) a b)
      (s1Config L (8*q+5) 1 a 0 b h) =
      some (s1Config L (8*q+4) 0
        (nextExponent 1 a b) 0 (nextRight b) (h+5+3*b)) := by
  simpa only [m1ResidueFiveNextExponent_one_eq,
    m1ResidueFiveNextRight_eq] using
    m1ResidueFive_counted_increment_source L q a b h hL hbound ha

#print axioms m1ResidueFive_binDec
#print axioms m1ResidueFour_binDec
#print axioms m1ResidueFive_q4_prefix_run
#print axioms m1ResidueFive_q4_prefix_leftFacing
#print axioms m1ResidueFive_q4_prefix_rightShape
#print axioms m1ResidueFive_reset_prefix_to_s1
#print axioms m1ResidueFive_counted_increment_source
#print axioms m1ResidueFive_counted_increment_source_symbolic

end BB6Coverage.Agent24M1ResidueFive
