import CountedQ4Prefix
import Q4Suffix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48CountedInc0

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix

/-- The even n=6, m=1 branch reaches a q4 suffix after 44+12a moves.
The local bridge is shifted four cells to the right relative to the
m=2, odd-n q4 bridge. -/
def m1EvenQ4Inside (x : Int) : Bool := decide (-9 ≤ x ∧ x ≤ 4)

def m1EvenQ4BridgeStart : FConfig :=
  ⟨3, 0, [-7,-6,-5,-4,-1,2,3,4]⟩

def m1EvenQ4BridgeEnd : FConfig :=
  ⟨4, 5, [-9,-8,-7,-4,-1,1,2,3,4]⟩

theorem m1EvenQ4Bridge_exact :
    fRun tm2 41 m1EvenQ4BridgeStart = some m1EvenQ4BridgeEnd := by
  decide

theorem m1EvenQ4Bridge_heads :
    (List.range 41).all (fun k =>
      match fRun tm2 k m1EvenQ4BridgeStart with
      | none => true
      | some f => m1EvenQ4Inside f.head) = true := by
  decide

private theorem binDec_three_six :
    binDec 3 6 = d1 ++ d0 ++ d0 := by
  have h1 : binDec 3 6 = d1 ++ binDec 2 3 := by
    simpa using binDec_even 2 3 (by norm_num)
  have h2 : binDec 2 3 = d0 ++ binDec 1 1 := by
    simpa using binDec_odd 1 1 (by norm_num)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by norm_num)
  simp [h1,h2,h3,binDec_zero]

private theorem m1EvenSourceLeftAt (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 6 1 a 0 b h).tape
      (h - ((3*a+1+k : Nat) : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh) (1+k) := by
  have hleft :
      s1LeftFacing 3 6 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing, binDec_zero, binDec_three_six, List.append_assoc]
  have hcell := s1Config_left_cell 3 6 1 a 0 b h (3*a+1+k)
  have hside := sideBit_d1pow_append a (3*a+1+k)
    (markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh) (by omega)
  rw [hleft, hside] at hcell
  exact hcell

private theorem m1EvenSweptLeftCell (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a+1) (s1Config 3 6 1 a 0 b h).tape h
      (h - ((3*a+1 : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh) (1+k) := by
  have hpres := sweptLeft_preserves_left (3*a+1)
    (s1Config 3 6 1 a 0 b h).tape h
    (h - ((3*a+1 : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m1EvenSourceLeftAt a b h k
  have hcoord :
      h - ((3*a+1 : Nat) : Int) - (k : Int) =
        h - ((3*a+1+k : Nat) : Int) := by omega
  simpa [hcoord] using hsrc

/-- After the counted left sweep over 3a+1 leading ones, the complete
[-9,4] input window is the fixed 41-step bridge above. -/
theorem m1EvenQ4Bridge_input_match (a b : Nat) (h : Int) :
    ∀ y, m1EvenQ4Inside y = true →
      (sweptLeft (3*a+1) (s1Config 3 6 1 a 0 b h).tape h)
        (h - ((3*a+1 : Nat) : Int) + y) =
          decide (y ∈ m1EvenQ4BridgeStart.marked) := by
  intro y hy
  have hyb : -9 ≤ y ∧ y ≤ 4 := by
    simpa [m1EvenQ4Inside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a+1 : Nat) : Int) + y =
          h - ((3*a+1 : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m1EvenSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh) (1+k) =
          decide (y ∈ m1EvenQ4BridgeStart.marked) := by
      interval_cases y <;>
        norm_num [k, m1EvenQ4BridgeStart, markerWord, d0, d1, lh, sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    interval_cases y
    · have hleft := sweptLeft_leftmost (3*a)
        (s1Config 3 6 1 a 0 b h).tape h
      have hcoord :
          h - ((3*a+1 : Nat) : Int) + 1 =
            h - ((3*a : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m1EvenQ4BridgeStart] using hleft
    · by_cases ha : a = 0
      · subst a
        have hplus := sweptLeft_plus1 0
          (s1Config 3 6 1 0 0 b h).tape h
        have hcoord :
            h - ((1 : Nat) : Int) + 2 = h+1 := by omega
        rw [hcoord]
        simpa [m1EvenQ4BridgeStart] using hplus
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-2)
          (s1Config 3 6 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 2 =
              h - ((3*a+1-2 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1EvenQ4BridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config 3 6 1 0 0 b h).tape h (h+2) (by omega)
        have hsrc : (s1Config 3 6 1 0 0 b h).tape (h+2) = true := by
          have hc := s1Config_right_cell 3 6 1 0 0 b h 1
          simpa [s0RightFacing] using hc
        have hcoord :
            h - ((1 : Nat) : Int) + 3 = h+2 := by omega
        rw [hcoord, hpres]
        simpa [m1EvenQ4BridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-3)
          (s1Config 3 6 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 3 =
              h - ((3*a+1-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1EvenQ4BridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config 3 6 1 0 0 b h).tape h (h+3) (by omega)
        have hsrc : (s1Config 3 6 1 0 0 b h).tape (h+3) = true := by
          have hc := s1Config_right_cell 3 6 1 0 0 b h 2
          simpa [s0RightFacing] using hc
        have hcoord :
            h - ((1 : Nat) : Int) + 4 = h+3 := by omega
        rw [hcoord, hpres]
        simpa [m1EvenQ4BridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-4)
          (s1Config 3 6 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 4 =
              h - ((3*a+1-4 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1EvenQ4BridgeStart] using hblock

/-- Explicit tape at the even m=1,n=6 q4 cut. -/
def m1EvenQ4CutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 6 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m1EvenQ4Inside m1EvenQ4BridgeEnd).tape

/-- Source-connected m=1,n=6 even q4 cut:
44+12a primitive moves from S1 reach state 4 at head h+4.
The q4 suffix can then be entered after four already-consumed
state-4-on-one moves. -/
theorem m1Even_q4_prefix_run (a b : Nat) (h : Int) :
    run tm2 (44+12*a)
      ⟨3,h,(s1Config 3 6 1 a 0 b h).tape⟩ =
      some ⟨4,h+4,m1EvenQ4CutTape a b h⟩ := by
  let T := (s1Config 3 6 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m1EvenQ4Inside m1EvenQ4BridgeEnd).tape
  have hleftFacing :
      s1LeftFacing 3 6 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing, binDec_zero, binDec_three_six, List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 6 1 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 6 1 a 0) i = true := by
      rw [hleftFacing]
      by_cases hi3 : i < 3*a
      · have hiLen : i < (d1pow a).length := by
          simpa [d1pow_length] using hi3
        rw [sideBit_append_left (d1pow a)
          (markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh) i hiLen]
        exact sideBit_d1pow_true a i hi3
      · have hieq : i = 3*a := by omega
        subst i
        have hlen : (d1pow a).length = 3*a := by simp [d1pow_length]
        rw [sideBit_append_right (d1pow a)
          (markerWord 1 ++ d0 ++ d1 ++ d0 ++ lh) (3*a) (by simpa [hlen])]
        simp [markerWord, d1pow_length]
    simpa [T] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 6 1 a 0 b h 0
    simpa [T,s0RightFacing] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m1EvenQ4Bridge_input_match a b h
  have hBridge := bridgeAt T1 hN m1EvenQ4Inside
    m1EvenQ4BridgeStart m1EvenQ4BridgeEnd 41 rfl
    m1EvenQ4Bridge_exact m1EvenQ4Bridge_heads hmatch
  have hBridge' :
      run tm2 41 ⟨3,hN,T1⟩ = some ⟨4,hN+5,T2⟩ := by
    simpa [T2,frameAt,shiftConfig,m1EvenQ4BridgeEnd] using hBridge
  have hlinear : linearRightOnes T2 (hN+5) (3*a) := by
    intro i hi
    let x : Int := hN+5+(i:Int)
    have hout : m1EvenQ4Inside (x-hN) = false := by
      simp [m1EvenQ4Inside,x]
      omega
    have hframe : T2 x = T1 x := by
      simpa [T2] using
        frameAt_tape_outside T1 hN m1EvenQ4Inside
          m1EvenQ4BridgeEnd x hout
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
        rw [hcoord] at hblock
        exact hblock
      · by_cases hx1 : x = h+1
        · subst x
          exact sweptLeft_plus1 N T h
        · have hx2 : h+2 ≤ x := by omega
          have hpres := sweptLeft_preserves_right N T h x hx2
          have hx23 : x = h+2 ∨ x = h+3 := by
            dsimp [x,N,hN] at *
            omega
          rcases hx23 with hx2' | hx3'
          · rw [hx2'] at hpres
            have hsrc : T (h+2) = true := by
              simpa [T,s0RightFacing] using
                s1Config_right_cell 3 6 1 a 0 b h 1
            simpa [hsrc] using hpres
          · rw [hx3'] at hpres
            have hsrc : T (h+3) = true := by
              simpa [T,s0RightFacing] using
                s1Config_right_cell 3 6 1 a 0 b h 2
            simpa [hsrc] using hpres
    simpa [x,T2] using hframe.trans hT1
  have hScan := E_scan T2 (hN+5) (3*a) hlinear
  have hhead : hN+5+(3*a:Int) = h+4 := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*a) ⟨4,hN+5,T2⟩ = some ⟨4,h+4,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(41+3*a)) ⟨3,h,T⟩ =
      some ⟨4,h+4,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 44+12*a = 3*N+(41+3*a) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m1EvenQ4CutTape,hnum] using htotal

end BB6Coverage.Agent48CountedInc0
