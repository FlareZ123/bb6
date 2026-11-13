/-!
# Source-level m=1,n=3 odd q4 reset prefix

A parameterized Lean proof candidate for the TM63 S1 reset stage
S1(3,3,1,a,0,b) -> S1(3,2,0,a+b+2,2^b-1,0).
The finite 29-step bridge is kernel-decidable and its head path is
confined to [-9,4]. This module has not yet been compiled in CI.
Keep it in im-results/ until compilation and axiom audit succeed.
-/

import CountedReset
import ChampionRootBridge
import S1Encoder
import CountedQ4Prefix
import Q4Suffix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24M1OddQ4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset

/-- The odd n=3, m=1 branch reaches a q4 suffix after 32+12a moves.
The local bridge is shifted four cells to the right relative to the
m=2, odd-n q4 bridge. -/
def m1OddQ4Inside (x : Int) : Bool := decide (-9 ≤ x ∧ x ≤ 4)

def m1OddQ4BridgeStart : FConfig :=
  ⟨3, 0, [-7,-4,-1,2,3,4]⟩

def m1OddQ4BridgeEnd : FConfig :=
  ⟨4, 5, [4,3,2,1,-1,-4,-5,-6,-7]⟩

theorem m1OddQ4Bridge_exact :
    fRun tm2 29 m1OddQ4BridgeStart = some m1OddQ4BridgeEnd := by
  decide

theorem m1OddQ4Bridge_heads :
    (List.range 29).all (fun k =>
      match fRun tm2 k m1OddQ4BridgeStart with
      | none => true
      | some f => m1OddQ4Inside f.head) = true := by
  decide



private theorem binDec_three_three :
    binDec 3 3 = d0 ++ d0 ++ d1 := by
  have h1 : binDec 3 3 = d0 ++ binDec 2 1 := by
    simpa using binDec_odd 2 1 (by decide)
  have h2 : binDec 2 1 = d0 ++ binDec 1 0 := by
    simpa using binDec_odd 1 0 (by decide)
  have h3 : binDec 1 0 = d1 ++ binDec 0 0 := by
    simpa using binDec_even 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]



private theorem m1OddSourceLeftAt (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 3 1 a 0 b h).tape
      (h - ((3*a+1+k : Nat) : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d0 ++ d1 ++ lh) (1+k) := by
  have hleft :
      s1LeftFacing 3 3 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1 ++ lh := by
    simp [s1LeftFacing, binDec_zero, binDec_three_three, List.append_assoc]
  have hcell := s1Config_left_cell 3 3 1 a 0 b h (3*a+1+k)
  have hside := sideBit_d1pow_append a (3*a+1+k)
    (markerWord 1 ++ d0 ++ d0 ++ d1 ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc,
    show 3*a+1+k-3*a = 1+k by omega] using hcell

private theorem m1OddSweptLeftCell (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a+1) (s1Config 3 3 1 a 0 b h).tape h
      (h - ((3*a+1 : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d0 ++ d1 ++ lh) (1+k) := by
  have hpres := sweptLeft_preserves_left (3*a+1)
    (s1Config 3 3 1 a 0 b h).tape h
    (h - ((3*a+1 : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m1OddSourceLeftAt a b h k
  have hcoord :
      h - ((3*a+1 : Nat) : Int) - (k : Int) =
        h - ((3*a+1+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the counted left sweep over 3a+1 leading ones, the complete
[-9,4] input window is the fixed 41-step bridge above. -/
theorem m1OddQ4Bridge_input_match (a b : Nat) (h : Int) :
    ∀ y, m1OddQ4Inside y = true →
      (sweptLeft (3*a+1) (s1Config 3 3 1 a 0 b h).tape h)
        (h - ((3*a+1 : Nat) : Int) + y) =
          decide (y ∈ m1OddQ4BridgeStart.marked) := by
  intro y hy
  have hyb : -9 ≤ y ∧ y ≤ 4 := by
    simpa [m1OddQ4Inside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a+1 : Nat) : Int) + y =
          h - ((3*a+1 : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m1OddSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 1 ++ d0 ++ d0 ++ d1 ++ lh) (1+k) =
          decide (y ∈ m1OddQ4BridgeStart.marked) := by
      have hyCases : y = -9 ∨ y = -8 ∨ y = -7 ∨ y = -6 ∨ y = -5 ∨
          y = -4 ∨ y = -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h9 | h8 | h7 | h6 | h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k, m1OddQ4BridgeStart, markerWord, d0, d1, lh, sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega
    rcases hyCases with h1 | h2 | h3 | h4
    all_goals subst y
    · have hleft := sweptLeft_leftmost (3*a)
        (s1Config 3 3 1 a 0 b h).tape h
      have hcoord :
          h - ((3*a+1 : Nat) : Int) + 1 =
            h - ((3*a : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m1OddQ4BridgeStart] using hleft
    · by_cases ha : a = 0
      · subst a
        have hplus := sweptLeft_plus1 0
          (s1Config 3 3 1 0 0 b h).tape h
        have hcoord :
            h - ((1 : Nat) : Int) + 2 = h+1 := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hplus
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-2)
          (s1Config 3 3 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 2 =
              h - ((3*a+1-2 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config 3 3 1 0 0 b h).tape h (h+2) (by omega)
        have hsrc : (s1Config 3 3 1 0 0 b h).tape (h+2) = true := by
          have hc := s1Config_right_cell 3 3 1 0 0 b h 1
          have hcoord : h+1+1 = h+2 := by omega
          simpa [hcoord,s1PhysicalRight_source, sideBit] using hc
        have hcoord :
            h - ((1 : Nat) : Int) + 3 = h+2 := by omega
        rw [hcoord, hpres]
        simpa [m1OddQ4BridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-3)
          (s1Config 3 3 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 3 =
              h - ((3*a+1-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config 3 3 1 0 0 b h).tape h (h+3) (by omega)
        have hsrc : (s1Config 3 3 1 0 0 b h).tape (h+3) = true := by
          have hc := s1Config_right_cell 3 3 1 0 0 b h 2
          have hcoord : h+1+2 = h+3 := by omega
          simpa [hcoord,s1PhysicalRight_source, sideBit] using hc
        have hcoord :
            h - ((1 : Nat) : Int) + 4 = h+3 := by omega
        rw [hcoord, hpres]
        simpa [m1OddQ4BridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-4)
          (s1Config 3 3 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 4 =
              h - ((3*a+1-4 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hblock

/-- Explicit tape at the odd m=1,n=3 q4 cut. -/
def m1OddQ4CutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 3 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m1OddQ4Inside m1OddQ4BridgeEnd).tape

/-- Source-connected m=1,n=3 odd q4 cut:
44+12a primitive moves from S1 reach state 4 at head h+4.
The q4 suffix can then be entered after four already-consumed
state-4-on-one moves. -/
theorem m1Odd_q4_prefix_run (a b : Nat) (h : Int) :
    run tm2 (32+12*a)
      ⟨3,h,(s1Config 3 3 1 a 0 b h).tape⟩ =
      some ⟨4,h+4,m1OddQ4CutTape a b h⟩ := by
  let T := (s1Config 3 3 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m1OddQ4Inside m1OddQ4BridgeEnd).tape
  have hleftFacing :
      s1LeftFacing 3 3 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1 ++ lh := by
    simp [s1LeftFacing, binDec_zero, binDec_three_three, List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 3 1 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 3 1 a 0) i = true := by
      rw [hleftFacing]
      let R : List Bool := markerWord 1 ++ (d0 ++ (d1 ++ (d0 ++ (d0 ++ lh))))
      simp only [List.append_assoc]
      change sideBit (d1pow a ++ R) i = true
      by_cases hi3 : i < 3*a
      · have hiLen : i < (d1pow a).length := by
          simpa [d1pow_length] using hi3
        rw [sideBit_append_left (d1pow a) R i hiLen]
        exact sideBit_d1pow_true a i hi3
      · have hieq : i = 3*a := by omega
        subst i
        have hlen : (d1pow a).length = 3*a := by simp [d1pow_length]
        rw [sideBit_append_right (d1pow a) R (3*a) (by simpa [hlen])]
        simp [markerWord, d1pow_length]
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 3 1 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m1OddQ4Bridge_input_match a b h
  have hBridge := bridgeAt T1 hN m1OddQ4Inside
    m1OddQ4BridgeStart m1OddQ4BridgeEnd 29 rfl
    m1OddQ4Bridge_exact m1OddQ4Bridge_heads hmatch
  have hBridge' :
      run tm2 29 ⟨3,hN,T1⟩ = some ⟨4,hN+5,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m1OddQ4Inside m1OddQ4BridgeEnd =
          (⟨4,hN+5,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m1OddQ4BridgeEnd]
      · simp [frameAt_head,m1OddQ4BridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+5) (3*a) := by
    intro i hi
    let x : Int := hN+5+(i:Int)
    have hout : m1OddQ4Inside (x-hN) = false := by
      simp [m1OddQ4Inside,x]
      omega
    have hframe : T2 x = T1 x := by
      simpa [T2] using
        frameAt_tape_outside T1 hN m1OddQ4Inside
          m1OddQ4BridgeEnd x hout
    have hT1 : T1 x = true := by
      by_cases hx : x ≤ h
      · let j : Nat := 3*a-4-i
        have hj : j+1 < N := by
          dsimp [j,N,x,hN] at *
          omega
        have hblock := sweptLeft_block N j T h hj
        have hcoord : x = h-(j:Int) := by
          dsimp [x,j,N,hN]
          omega
        change sweptLeft N T h x = true
        rw [hcoord]
        exact hblock
      · by_cases hx1 : x = h+1
        · rw [hx1]
          simpa [T1,N] using sweptLeft_plus1 (3*a) T h
        · have hx2 : h+2 ≤ x := by omega
          have hx23 : x = h+2 ∨ x = h+3 := by
            dsimp [x,N,hN] at *
            omega
          have hpres := sweptLeft_preserves_right N T h x (by omega)
          rcases hx23 with hx2' | hx3'
          · rw [hx2'] at hpres ⊢
            change sweptLeft N T h (h+2) = true
            have hsrc : T (h+2) = true := by
              have hcoord : h+1+1 = h+2 := by omega
              simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
                s1Config_right_cell 3 3 1 a 0 b h 1
            rw [hpres,hsrc]
          · rw [hx3'] at hpres ⊢
            change sweptLeft N T h (h+3) = true
            have hsrc : T (h+3) = true := by
              have hcoord : h+1+2 = h+3 := by omega
              simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
                s1Config_right_cell 3 3 1 a 0 b h 2
            rw [hpres,hsrc]
    simpa [x,T2] using hframe.trans hT1
  have hScan := E_scan T2 (hN+5) (3*a) hlinear
  have hhead : hN+5+(3*a:Int) = h+4 := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*a) ⟨4,hN+5,T2⟩ = some ⟨4,h+4,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(29+3*a)) ⟨3,h,T⟩ =
      some ⟨4,h+4,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 32+12*a = 3*N+(29+3*a) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m1OddQ4CutTape,hnum] using htotal



private theorem sideBit_false_after_length_local (xs : List Bool) (i : Nat)
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

private theorem m1OddQ4CutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m1OddQ4Inside (x-(h-((3*a+1 : Nat) : Int))) = false) :
    m1OddQ4CutTape a b h x =
      sweptLeft (3*a+1) (s1Config 3 3 1 a 0 b h).tape h x := by
  let T := (s1Config 3 3 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m1OddQ4Inside m1OddQ4BridgeEnd x hout
  simpa [m1OddQ4CutTape,T,N,T1] using hf

private theorem m1OddQ4CutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m1OddQ4Inside (x-(h-((3*a+1 : Nat) : Int))) = true) :
    m1OddQ4CutTape a b h x =
      decide ((x-(h-((3*a+1 : Nat) : Int))) ∈ m1OddQ4BridgeEnd.marked) := by
  let T := (s1Config 3 3 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m1OddQ4Inside m1OddQ4BridgeEnd x hin
  simpa [m1OddQ4CutTape,T,N,T1] using hf

private theorem m1OddQ4CutTape_eq_source_right
    (a b : Nat) (h x : Int) (hx : h+5 ≤ x) :
    m1OddQ4CutTape a b h x =
      (s1Config 3 3 1 a 0 b h).tape x := by
  let T := (s1Config 3 3 1 a 0 b h).tape
  have hout : m1OddQ4Inside
      (x-(h-((3*a+1 : Nat) : Int))) = false := by
    simp [m1OddQ4Inside]
    omega
  have hcut := m1OddQ4CutTape_eq_swept a b h x hout
  have hpres := sweptLeft_preserves_right (3*a+1) T h x (by omega)
  simpa [T] using hcut.trans hpres

/-- The explicit cut tape satisfies the right-shape contract of Q4Suffix.
The q4 guard is the five-cell block at h..h+4; the b-counter and its
blank terminator are untouched to the right of the bridge frame. -/
theorem m1Odd_q4_prefix_rightShape (a b : Nat) (h : Int) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape (m1OddQ4CutTape a b h) h b := by
  unfold BB6Coverage.Agent8Q4Suffix.q4RightShape
  let T := (s1Config 3 3 1 a 0 b h).tape
  constructor
  · intro i hi
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hiCases with h0 | h1 | h2 | h3 | h4
    all_goals subst i
    · by_cases ha0 : a = 0
      · subst a
        have hrel : h - (h-(1:Int)) = 1 := by omega
        have hin : m1OddQ4Inside ((h+0)-(h-(1:Int))) = true := by
          simp [m1OddQ4Inside,hrel]
        have hcut := m1OddQ4CutTape_eq_end_inside 0 b h (h+0) hin
        have hmark :
            decide (((h+0)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          have hcoord : (h+0)-(h-(1:Int)) = 1 := by omega
          rw [hcoord]
          simp [m1OddQ4BridgeEnd]
        exact hcut.trans hmark
      · by_cases ha1 : a = 1
        · subst a
          have hrel : h - (h-(4:Int)) = 4 := by omega
          have hin : m1OddQ4Inside ((h+0)-(h-(4:Int))) = true := by
            simp [m1OddQ4Inside,hrel]
          have hcut := m1OddQ4CutTape_eq_end_inside 1 b h (h+0) hin
          have hmark :
              decide (((h+0)-(h-(4:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
            have hcoord : (h+0)-(h-(4:Int)) = 4 := by omega
            rw [hcoord]
            simp [m1OddQ4BridgeEnd]
          exact hcut.trans hmark
        · have hout : m1OddQ4Inside
              ((h+0)-(h-((3*a+1 : Nat) : Int))) = false := by
            simp [m1OddQ4Inside]
            omega
          have hcut := m1OddQ4CutTape_eq_swept a b h (h+0) hout
          have hhead : sweptLeft (3*a+1) T h h = true := by
            have hs := sweptLeft_head (3*a+1-2) T h
            have hN : 3*a+1 = (3*a+1-2)+2 := by omega
            rw [← hN] at hs
            exact hs
          have hhead' : sweptLeft (3*a+1)
              (s1Config 3 3 1 a 0 b h).tape h (h+0) = true := by
            simpa [T] using hhead
          exact hcut.trans hhead'
    · by_cases ha0 : a = 0
      · subst a
        have hrel : (h+1) - (h-(1:Int)) = 2 := by omega
        have hin : m1OddQ4Inside ((h+1)-(h-(1:Int))) = true := by
          simp [m1OddQ4Inside,hrel]
        have hcut := m1OddQ4CutTape_eq_end_inside 0 b h (h+1) hin
        have hmark :
            decide (((h+1)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          simp [hrel,m1OddQ4BridgeEnd]
        simpa [hrel] using hcut.trans hmark
      · have hout : m1OddQ4Inside
            ((h+1)-(h-((3*a+1 : Nat) : Int))) = false := by
          simp [m1OddQ4Inside]
          omega
        have hcut := m1OddQ4CutTape_eq_swept a b h (h+1) hout
        have hplus : sweptLeft (3*a+1) T h (h+1) = true := by
          simpa [T] using sweptLeft_plus1 (3*a) T h
        simpa [T] using hcut.trans hplus
    · by_cases ha0 : a = 0
      · subst a
        have hrel : (h+2) - (h-(1:Int)) = 3 := by omega
        have hin : m1OddQ4Inside ((h+2)-(h-(1:Int))) = true := by
          simp [m1OddQ4Inside,hrel]
        have hcut := m1OddQ4CutTape_eq_end_inside 0 b h (h+2) hin
        have hmark :
            decide (((h+2)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          simp [hrel,m1OddQ4BridgeEnd]
        simpa [hrel] using hcut.trans hmark
      · have hout : m1OddQ4Inside
            ((h+2)-(h-((3*a+1 : Nat) : Int))) = false := by
          simp [m1OddQ4Inside]
          omega
        have hcut := m1OddQ4CutTape_eq_swept a b h (h+2) hout
        have hpres := sweptLeft_preserves_right (3*a+1) T h (h+2) (by omega)
        have hsrc : T (h+2) = true := by
          have hcoord : h+1+(1:Int) = h+2 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell 3 3 1 a 0 b h 1
        exact hcut.trans (hpres.trans hsrc)
    · by_cases ha0 : a = 0
      · subst a
        have hrel : (h+3) - (h-(1:Int)) = 4 := by omega
        have hin : m1OddQ4Inside ((h+3)-(h-(1:Int))) = true := by
          simp [m1OddQ4Inside,hrel]
        have hcut := m1OddQ4CutTape_eq_end_inside 0 b h (h+3) hin
        have hmark :
            decide (((h+3)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          simp [hrel,m1OddQ4BridgeEnd]
        simpa [hrel] using hcut.trans hmark
      · have hout : m1OddQ4Inside
            ((h+3)-(h-((3*a+1 : Nat) : Int))) = false := by
          simp [m1OddQ4Inside]
          omega
        have hcut := m1OddQ4CutTape_eq_swept a b h (h+3) hout
        have hpres := sweptLeft_preserves_right (3*a+1) T h (h+3) (by omega)
        have hsrc : T (h+3) = true := by
          have hcoord : h+1+(2:Int) = h+3 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell 3 3 1 a 0 b h 2
        exact hcut.trans (hpres.trans hsrc)
    · have hout : m1OddQ4Inside
          ((h+4)-(h-((3*a+1 : Nat) : Int))) = false := by
        simp [m1OddQ4Inside]
        omega
      have hcut := m1OddQ4CutTape_eq_swept a b h (h+4) hout
      have hpres := sweptLeft_preserves_right (3*a+1) T h (h+4) (by omega)
      have hsrc : T (h+4) = true := by
        have hcoord : h+1+(3:Int) = h+4 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 3 1 a 0 b h 3
      exact hcut.trans (hpres.trans hsrc)
  · constructor
    · have hcut := m1OddQ4CutTape_eq_source_right a b h (h+5) (by omega)
      have hsrc : T (h+5) = false := by
        have hcoord : h+1+(4:Int) = h+5 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 3 1 a 0 b h 4
      simpa [T] using hcut.trans hsrc
    · constructor
      · have hcut := m1OddQ4CutTape_eq_source_right a b h (h+6) (by omega)
        have hsrc : T (h+6) = false := by
          have hcoord : h+1+(5:Int) = h+6 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell 3 3 1 a 0 b h 5
        simpa [T] using hcut.trans hsrc
      · constructor
        · intro i hi
          have hcut := m1OddQ4CutTape_eq_source_right a b h (h+7+(i:Int)) (by omega)
          have hsrc : T (h+7+(i:Int)) =
              sideBit (s0RightFacing b) (6+i) := by
            have hcoord : h+1+(6+i:Int) = h+7+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit] using s1Config_right_cell 3 3 1 a 0 b h (6+i)
          have hside :
              sideBit (s0RightFacing b) (6+i) =
                sideBit (d1pow (b+1)) i := by
            rw [s0RightFacing]
            simpa using sideBit_append_right
              [false,true,true,true,false,false] (d1pow (b+1))
              (6+i) (by simp)
          have hones : sideBit (d1pow (b+1)) i = true :=
            sideBit_d1pow_true (b+1) i (by omega)
          have htarget : T (h+7+(i:Int)) = true := by
            rw [hsrc,hside,hones]
          exact hcut.trans htarget
        · intro i hi
          have hcut := m1OddQ4CutTape_eq_source_right a b h
            (h+10+(3*b:Int)+(i:Int)) (by omega)
          have hsrc : T (h+10+(3*b:Int)+(i:Int)) =
              sideBit (s0RightFacing b) (9+3*b+i) := by
            have hcoord : h+1+((9+3*b+i:Int)) =
                h+10+(3*b:Int)+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell 3 3 1 a 0 b h (9+3*b+i)
          have hlen : (s0RightFacing b).length = 9+3*b := by
            simp [s0RightFacing,d1pow_length]
            omega
          have hblank : sideBit (s0RightFacing b) (9+3*b+i) = false :=
            sideBit_false_after_length_local (s0RightFacing b)
              (9+3*b+i) (by omega)
          have htarget : T (h+10+(3*b:Int)+(i:Int)) = false := by
            rw [hsrc,hblank]
          exact hcut.trans htarget



/-- The cut preserves the entire blank suffix after the finite right-facing
unary counter, not merely the five-cell q4 guard. -/
theorem m1Odd_q4_prefix_far_tail (a b : Nat) (h : Int) :
    ∀ i : Nat, 9+3*b ≤ i →
      m1OddQ4CutTape a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hcut := m1OddQ4CutTape_eq_source_right a b h
    (h+1+(i:Int)) (by omega)
  have hsrc :
      (s1Config 3 3 1 a 0 b h).tape (h+1+(i:Int)) =
        sideBit (s0RightFacing b) i := by
    simpa [s1PhysicalRight_source,sideBit] using
      s1Config_right_cell 3 3 1 a 0 b h i
  have hlen : (s0RightFacing b).length = 9+3*b := by
    simp [s0RightFacing,d1pow_length]
    omega
  have hblank : sideBit (s0RightFacing b) i = false :=
    sideBit_false_after_length_local (s0RightFacing b) i (by omega)
  calc
    m1OddQ4CutTape a b h (h+1+(i:Int)) =
        (s1Config 3 3 1 a 0 b h).tape (h+1+(i:Int)) := hcut
    _ = sideBit (s0RightFacing b) i := hsrc
    _ = false := hblank


def m1OddQ4LeftFacing (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec 3 2 ++ lh

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  exact BB6Coverage.Agent6Q4Prefix.sideBit_append_right xs ys i hi

private theorem sideBit_binDec33_eq_binDec32_after3 (j : Nat)
    (hj : 3 ≤ j) :
    sideBit (d0 ++ d0 ++ d1 ++ lh) j =
      sideBit (d1 ++ d0 ++ d1 ++ lh) j := by
  have hs :
      sideBit (d0 ++ d0 ++ d1 ++ lh) j =
        sideBit (d0 ++ d1 ++ lh) (j-3) := by
    simpa [List.append_assoc,d0] using
      sideBit_append_after_local d0 (d0 ++ d1 ++ lh) j (by simp [d0]; omega)
  have ht :
      sideBit (d1 ++ d0 ++ d1 ++ lh) j =
        sideBit (d0 ++ d1 ++ lh) (j-3) := by
    simpa [List.append_assoc,d1] using
      sideBit_append_after_local d1 (d0 ++ d1 ++ lh) j (by simp [d1]; omega)
  rw [hs,ht]



private theorem m1OddQ4LeftFacingTail (a i : Nat)
    (hi : 3*a+11 ≤ i) :
    sideBit (s1LeftFacing 3 3 1 a 0) i =
      sideBit (m1OddQ4LeftFacing a) i := by
  have hsrc :
      s1LeftFacing 3 3 1 a 0 =
        (d1pow a ++ markerWord 1 ++ d0) ++
          (d0 ++ d0 ++ d1 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,binDec_three_three,List.append_assoc]
  have htgt :
      m1OddQ4LeftFacing a =
        ([true] ++ d1pow a ++ markerWord 0 ++ d0) ++
          (d1 ++ d0 ++ d1 ++ lh) := by
    simp [m1OddQ4LeftFacing,binDec_three_two,List.append_assoc]
  have hs := sideBit_append_after_local
    (d1pow a ++ markerWord 1 ++ d0) (d0 ++ d0 ++ d1 ++ lh) i (by
      simp [d1pow_length,markerWord,d0]
      omega)
  have ht := sideBit_append_after_local
    ([true] ++ d1pow a ++ markerWord 0 ++ d0) (d1 ++ d0 ++ d1 ++ lh) i (by
      simp [d1pow_length,markerWord,d0]
      omega)
  have hlenS : (d1pow a ++ markerWord 1 ++ d0).length = 3*a+6 := by
    simp [d1pow_length,markerWord,d0]
  have hlenT : ([true] ++ d1pow a ++ markerWord 0 ++ d0).length = 3*a+6 := by
    simp [d1pow_length,markerWord,d0]
  rw [hsrc,htgt,hs,ht]
  rw [hlenS,hlenT]
  apply sideBit_binDec33_eq_binDec32_after3
  omega



private theorem m1OddQ4LeftFacingPrefixTrue (a i : Nat)
    (hi : i ≤ 3*a) :
    sideBit (m1OddQ4LeftFacing a) i = true := by
  have hlist :
      m1OddQ4LeftFacing a =
        [true] ++ (d1pow a ++
          (markerWord 0 ++ d0 ++ binDec 3 2 ++ lh)) := by
    simp [m1OddQ4LeftFacing,List.append_assoc]
  by_cases hi0 : i = 0
  · subst i
    simp [hlist,sideBit]
  · have hpos : 1 ≤ i := by omega
    rw [hlist]
    rw [sideBit_append_after_local [true]
      (d1pow a ++ (markerWord 0 ++ d0 ++ binDec 3 2 ++ lh)) i
      (by simp; omega)]
    change sideBit (d1pow a ++ (markerWord 0 ++ d0 ++ binDec 3 2 ++ lh))
      (i-1) = true
    have hrest := sideBit_append_left (d1pow a)
      (markerWord 0 ++ d0 ++ binDec 3 2 ++ lh) (i-1) (by
        have hi' : i-1 < 3*a := by omega
        simpa [d1pow_length] using hi')
    rw [hrest]
    exact sideBit_d1pow_true a (i-1) (by omega)

private theorem m1OddQ4LeftFacingBoundaryBit (a k : Nat)
    (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    sideBit (m1OddQ4LeftFacing a) (3*a+1+k) =
      decide (-(k:Int) ∈ m1OddQ4BridgeEnd.marked) := by
  have hlist :
      m1OddQ4LeftFacing a =
        ([true] ++ d1pow a) ++
          (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) := by
    simp [m1OddQ4LeftFacing,binDec_three_two,List.append_assoc]
  rw [hlist]
  rw [sideBit_append_after_local ([true] ++ d1pow a)
    (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh)
    (3*a+1+k) (by simp [d1pow_length]; omega)]
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hkCases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  all_goals subst k
  all_goals simp [m1OddQ4BridgeEnd,markerWord,d0,d1,lh,sideBit,d1pow_length]



private theorem m1OddQ4CutTape_eq_source_left
    (a b : Nat) (h : Int) (i : Nat) (hi : 3*a+11 ≤ i) :
    m1OddQ4CutTape a b h (h-(i:Int)) =
      sideBit (s1LeftFacing 3 3 1 a 0) i := by
  let T := (s1Config 3 3 1 a 0 b h).tape
  have hout : m1OddQ4Inside
      ((h-(i:Int))-(h-((3*a+1 : Nat) : Int))) = false := by
    simp [m1OddQ4Inside]
    omega
  have hcut := m1OddQ4CutTape_eq_swept a b h
    (h-(i:Int)) hout
  have hpres := sweptLeft_preserves_left (3*a+1) T h
    (h-(i:Int)) (by omega)
  have hcell := s1Config_left_cell 3 3 1 a 0 b h i
  simpa [T] using hcut.trans (hpres.trans hcell)



/-- Canonical left-facing tape at the m=1,n=3 odd q4 cut.  This is the
single remaining interface needed to identify the composed Q4 suffix
frame with the next S1 reset state. -/
theorem m1Odd_q4_prefix_leftFacing (a b : Nat) (h : Int) :
    ∀ i : Nat, m1OddQ4CutTape a b h (h-(i:Int)) =
      sideBit (m1OddQ4LeftFacing a) i := by
  intro i
  by_cases hi0 : i = 0
  · subst i
    have hshape := m1Odd_q4_prefix_rightShape a b h
    have htrue : m1OddQ4CutTape a b h h = true := by
      simpa using hshape.1 0 (by omega)
    simpa [m1OddQ4LeftFacing,sideBit] using htrue
  · by_cases hsmall : i+1 < 3*a+1
    · let x : Int := h-(i:Int)
      let r : Int := (3*a+1 : Nat) - (i:Int)
      have hrel : x-(h-((3*a+1 : Nat):Int)) = r := by
        dsimp [x,r]
        omega
      have htarget := m1OddQ4LeftFacingPrefixTrue a i (by omega)
      by_cases hin : m1OddQ4Inside r = true
      · have hin' : m1OddQ4Inside
            (x-(h-((3*a+1 : Nat):Int))) = true := by
          rw [hrel]
          exact hin
        have hcut := m1OddQ4CutTape_eq_end_inside a b h x hin'
        have hbounds : 2 ≤ r ∧ r ≤ 4 := by
          have hb : -9 ≤ r ∧ r ≤ 4 := by
            simpa [m1OddQ4Inside] using hin
          constructor <;> omega
        have hmark : decide (r ∈ m1OddQ4BridgeEnd.marked) = true := by
          have hcases : r=2 ∨ r=3 ∨ r=4 := by omega
          rcases hcases with h2 | h3 | h4
          · subst r; simp [m1OddQ4BridgeEnd]
          · subst r; simp [m1OddQ4BridgeEnd]
          · subst r; simp [m1OddQ4BridgeEnd]
        have hmark' : decide
            ((x-(h-((3*a+1 : Nat):Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          rw [hrel]
          exact hmark
        have hval : m1OddQ4CutTape a b h x = true :=
          hcut.trans hmark'
        exact hval.trans htarget.symm
      · have hout : m1OddQ4Inside r = false := by
          cases hb : m1OddQ4Inside r <;> simp_all
        have hout' : m1OddQ4Inside
            (x-(h-((3*a+1 : Nat):Int))) = false := by
          rw [hrel]
          exact hout
        have hcut := m1OddQ4CutTape_eq_swept a b h x hout'
        have hblock := sweptLeft_block (3*a+1) i
          (s1Config 3 3 1 a 0 b h).tape h (by omega)
        have hblock' :
            sweptLeft (3*a+1) (s1Config 3 3 1 a 0 b h).tape h x = true := by
          simpa [x] using hblock
        have hval : m1OddQ4CutTape a b h x = true := hcut.trans hblock'
        exact hval.trans htarget.symm
    · by_cases hieq : i = 3*a
      · have htarget := m1OddQ4LeftFacingPrefixTrue a i (by omega)
        let x : Int := h-(i:Int)
        have hrel : x-(h-((3*a+1 : Nat):Int)) = 1 := by
          dsimp [x]
          omega
        have hin : m1OddQ4Inside 1 = true := by
          simp [m1OddQ4Inside]
        have hin' : m1OddQ4Inside
            (x-(h-((3*a+1 : Nat):Int))) = true := by
          rw [hrel]
          exact hin
        have hcut := m1OddQ4CutTape_eq_end_inside a b h x hin'
        have hmark : decide (1 ∈ m1OddQ4BridgeEnd.marked) = true := by
          simp [m1OddQ4BridgeEnd]
        have hmark' : decide
            ((x-(h-((3*a+1 : Nat):Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          rw [hrel]
          exact hmark
        have hval : m1OddQ4CutTape a b h x = true :=
          hcut.trans hmark'
        exact hval.trans htarget.symm
      · by_cases hnext : i = 3*a+1
        · let x : Int := h-(i:Int)
          have hrel : x-(h-((3*a+1 : Nat):Int)) = 0 := by
            dsimp [x]
            omega
          have hin : m1OddQ4Inside 0 = true := by
            simp [m1OddQ4Inside]
          have hin' : m1OddQ4Inside
              (x-(h-((3*a+1 : Nat):Int))) = true := by
            rw [hrel]
            exact hin
          have hcut := m1OddQ4CutTape_eq_end_inside a b h x hin'
          have hmark : decide (0 ∈ m1OddQ4BridgeEnd.marked) = false := by
            simp [m1OddQ4BridgeEnd]
          have htarget : sideBit (m1OddQ4LeftFacing a) i = false := by
            subst i
            have hlist :
                m1OddQ4LeftFacing a =
                  ([true] ++ d1pow a) ++
                    (markerWord 0 ++ d0 ++ binDec 3 2 ++ lh) := by
              simp [m1OddQ4LeftFacing,List.append_assoc]
            rw [hlist]
            rw [sideBit_append_after_local ([true] ++ d1pow a)
              (markerWord 0 ++ d0 ++ binDec 3 2 ++ lh) (3*a+1)
              (by simp [d1pow_length])]
            simp [markerWord,sideBit]
          have hmark' : decide
              ((x-(h-((3*a+1 : Nat):Int))) ∈ m1OddQ4BridgeEnd.marked) = false := by
            rw [hrel]
            exact hmark
          have hval : m1OddQ4CutTape a b h x = false :=
            hcut.trans hmark'
          exact hval.trans htarget.symm
        · by_cases hbound : i ≤ 3*a+10
          · let k : Nat := i-(3*a+1)
            have hk1 : 1 ≤ k := by dsimp [k]; omega
            have hk9 : k ≤ 9 := by dsimp [k]; omega
            let x : Int := h-(i:Int)
            have hrel : x-(h-((3*a+1 : Nat):Int)) = -(k:Int) := by
              dsimp [x,k]
              omega
            have hin : m1OddQ4Inside (-(k:Int)) = true := by
              simp [m1OddQ4Inside]
              omega
            have hin' : m1OddQ4Inside
                (x-(h-((3*a+1 : Nat):Int))) = true := by
              rw [hrel]
              exact hin
            have hcut := m1OddQ4CutTape_eq_end_inside a b h x hin'
            have hi : i = 3*a+1+k := by
              dsimp [k]
              omega
            have htarget := m1OddQ4LeftFacingBoundaryBit a k hk1 hk9
            have htarget' :
                sideBit (m1OddQ4LeftFacing a) i =
                  decide (-(k:Int) ∈ m1OddQ4BridgeEnd.marked) := by
              rw [hi]
              exact htarget
            have hmark' : decide
                ((x-(h-((3*a+1 : Nat):Int))) ∈ m1OddQ4BridgeEnd.marked) =
                  decide (-(k:Int) ∈ m1OddQ4BridgeEnd.marked) := by
              rw [hrel]
            have hval :
                m1OddQ4CutTape a b h x =
                  sideBit (m1OddQ4LeftFacing a) i := by
              calc
                m1OddQ4CutTape a b h x =
                    decide ((x-(h-((3*a+1 : Nat):Int))) ∈
                      m1OddQ4BridgeEnd.marked) := hcut
                _ = decide (-(k:Int) ∈ m1OddQ4BridgeEnd.marked) := hmark'
                _ = sideBit (m1OddQ4LeftFacing a) i := htarget'.symm
            exact hval
          · have htail := m1OddQ4CutTape_eq_source_left a b h i (by omega)
            have hbits := m1OddQ4LeftFacingTail a i (by omega)
            exact htail.trans hbits



/-- Algebraic endpoint identity for the m=1,n=3 branch.  Combined with
the q4 suffix's d0-sweep left-facing tape formula, this yields the
canonical target marker-0 S1 left stream. -/
theorem m1OddQ4SuffixTargetLeft (a b : Nat) :
    s1LeftFacing 3 2 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++ (m1OddQ4LeftFacing a).drop 1 := by
  unfold s1LeftFacing m1OddQ4LeftFacing
  rw [binDec_pow2_sub_one]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc]



theorem m1Odd_resetPrefixCost_eq (a b : Nat) :
    resetPrefixCost 1 3 a b = 67+12*a+3*b := by
  have hv : BB6ChampionArithmetic.v2 3 = 0 :=
    v2_of_odd 3 (by decide)
  simp [resetPrefixCost,hv]
  omega



end BB6Coverage.Agent24M1OddQ4Prefix