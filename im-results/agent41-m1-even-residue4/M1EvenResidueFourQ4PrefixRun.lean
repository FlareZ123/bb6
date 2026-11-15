import CountedReset
import ChampionRootBridge
import S1Encoder
import CountedQ4Prefix
import Q4Suffix
import M1EvenResidueFourBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent41M1EvenResidueFour

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset

private theorem binDec_three_four :
    binDec 3 4 = d1 ++ d1 ++ d0 := by
  have h1 : binDec 3 4 = d1 ++ binDec 2 2 := by
    simpa using binDec_even 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m1EvenResidueFourSourceLeftAt
    (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 4 1 a 0 b h).tape
      (h - ((3*a+1+k : Nat) : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) (1+k) := by
  have hleft :
      s1LeftFacing 3 4 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing, binDec_zero, binDec_three_four, List.append_assoc]
  have hcell := s1Config_left_cell 3 4 1 a 0 b h (3*a+1+k)
  have hside := sideBit_d1pow_append a (3*a+1+k)
    (markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc,
    show 3*a+1+k-3*a = 1+k by omega] using hcell

private theorem m1EvenResidueFourSweptLeftCell
    (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a+1) (s1Config 3 4 1 a 0 b h).tape h
      (h - ((3*a+1 : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) (1+k) := by
  have hpres := sweptLeft_preserves_left (3*a+1)
    (s1Config 3 4 1 a 0 b h).tape h
    (h - ((3*a+1 : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m1EvenResidueFourSourceLeftAt a b h k
  have hcoord :
      h - ((3*a+1 : Nat) : Int) - (k : Int) =
        h - ((3*a+1+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the counted left sweep over 3a+1 leading ones, the complete
[-12,5] input window is the fixed 53-step residue-four bridge. -/
theorem m1EvenResidueFourBridge_input_match
    (a b : Nat) (h : Int) :
    ∀ y, m1EvenResidueFourInside y = true →
      (sweptLeft (3*a+1) (s1Config 3 4 1 a 0 b h).tape h)
        (h - ((3*a+1 : Nat) : Int) + y) =
          decide (y ∈ m1EvenResidueFourBridgeStart.marked) := by
  intro y hy
  have hyb : -12 ≤ y ∧ y ≤ 5 := by
    simpa [m1EvenResidueFourInside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a+1 : Nat) : Int) + y =
          h - ((3*a+1 : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m1EvenResidueFourSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) (1+k) =
          decide (y ∈ m1EvenResidueFourBridgeStart.marked) := by
      have hyCases : y = -12 ∨ y = -11 ∨ y = -10 ∨ y = -9 ∨
          y = -8 ∨ y = -7 ∨ y = -6 ∨ y = -5 ∨ y = -4 ∨
          y = -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h12 | h11 | h10 | h9 | h8 | h7 | h6 |
          h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k, m1EvenResidueFourBridgeStart,
        markerWord, d0, d1, lh, sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 := by omega
    rcases hyCases with h1 | h2 | h3 | h4 | h5
    all_goals subst y
    · have hleft := sweptLeft_leftmost (3*a)
        (s1Config 3 4 1 a 0 b h).tape h
      have hcoord :
          h - ((3*a+1 : Nat) : Int) + 1 =
            h - ((3*a : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m1EvenResidueFourBridgeStart] using hleft
    · by_cases ha : a = 0
      · subst a
        have hplus := sweptLeft_plus1 0
          (s1Config 3 4 1 0 0 b h).tape h
        have hcoord :
            h - ((1 : Nat) : Int) + 2 = h+1 := by omega
        rw [hcoord]
        simpa [m1EvenResidueFourBridgeStart] using hplus
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-2)
          (s1Config 3 4 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 2 =
              h - ((3*a+1-2 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1EvenResidueFourBridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config 3 4 1 0 0 b h).tape h (h+2) (by omega)
        have hsrc : (s1Config 3 4 1 0 0 b h).tape (h+2) = true := by
          have hc := s1Config_right_cell 3 4 1 0 0 b h 1
          have hcoord : h+1+1 = h+2 := by omega
          simpa [hcoord,s1PhysicalRight_source,sideBit] using hc
        have hcoord :
            h - ((1 : Nat) : Int) + 3 = h+2 := by omega
        rw [hcoord,hpres]
        simpa [m1EvenResidueFourBridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-3)
          (s1Config 3 4 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 3 =
              h - ((3*a+1-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1EvenResidueFourBridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config 3 4 1 0 0 b h).tape h (h+3) (by omega)
        have hsrc : (s1Config 3 4 1 0 0 b h).tape (h+3) = true := by
          have hc := s1Config_right_cell 3 4 1 0 0 b h 2
          have hcoord : h+1+2 = h+3 := by omega
          simpa [hcoord,s1PhysicalRight_source,sideBit] using hc
        have hcoord :
            h - ((1 : Nat) : Int) + 4 = h+3 := by omega
        rw [hcoord,hpres]
        simpa [m1EvenResidueFourBridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-4)
          (s1Config 3 4 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 4 =
              h - ((3*a+1-4 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1EvenResidueFourBridgeStart] using hblock
    · by_cases ha0 : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config 3 4 1 0 0 b h).tape h (h+4) (by omega)
        have hsrc : (s1Config 3 4 1 0 0 b h).tape (h+4) = true := by
          have hc := s1Config_right_cell 3 4 1 0 0 b h 3
          have hcoord : h+1+3 = h+4 := by omega
          simpa [hcoord,s1PhysicalRight_source,sideBit] using hc
        have hcoord :
            h - ((1 : Nat) : Int) + 5 = h+4 := by omega
        rw [hcoord,hpres]
        simpa [m1EvenResidueFourBridgeStart] using hsrc
      · by_cases ha1 : a = 1
        · subst a
          have hplus := sweptLeft_plus1 3
            (s1Config 3 4 1 1 0 b h).tape h
          have hcoord :
              h - ((4 : Nat) : Int) + 5 = h+1 := by omega
          rw [hcoord]
          simpa [m1EvenResidueFourBridgeStart] using hplus
        · have hblock := sweptLeft_block (3*a+1) (3*a+1-5)
            (s1Config 3 4 1 a 0 b h).tape h (by omega)
          have hcoord :
              h - ((3*a+1 : Nat) : Int) + 5 =
                h - ((3*a+1-5 : Nat) : Int) := by omega
          rw [hcoord]
          simpa [m1EvenResidueFourBridgeStart] using hblock

/-- Explicit tape at the m=1,n=8k+4 residue-four q4 cut (base k=0). -/
def m1EvenResidueFourCutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 4 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m1EvenResidueFourInside
    m1EvenResidueFourBridgeEnd).tape

private theorem m1EvenResidueFourCutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m1EvenResidueFourInside
      (x-(h-((3*a+1 : Nat) : Int))) = false) :
    m1EvenResidueFourCutTape a b h x =
      sweptLeft (3*a+1) (s1Config 3 4 1 a 0 b h).tape h x := by
  let T := (s1Config 3 4 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m1EvenResidueFourInside m1EvenResidueFourBridgeEnd x hout
  simpa [m1EvenResidueFourCutTape,T,N,T1] using hf

private theorem m1EvenResidueFourCutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m1EvenResidueFourInside
      (x-(h-((3*a+1 : Nat) : Int))) = true) :
    m1EvenResidueFourCutTape a b h x =
      decide ((x-(h-((3*a+1 : Nat) : Int))) ∈
        m1EvenResidueFourBridgeEnd.marked) := by
  let T := (s1Config 3 4 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m1EvenResidueFourInside m1EvenResidueFourBridgeEnd x hin
  simpa [m1EvenResidueFourCutTape,T,N,T1] using hf

/-- Source-connected base q4 prefix for m=1,n=4: after 56+12a
original TM2 moves, state 4 is at h+4 on the explicit q4 cut tape. -/
theorem m1EvenResidueFour_q4_prefix_run (a b : Nat) (h : Int) :
    run tm2 (56+12*a)
      ⟨3,h,(s1Config 3 4 1 a 0 b h).tape⟩ =
      some ⟨4,h+4,m1EvenResidueFourCutTape a b h⟩ := by
  let T := (s1Config 3 4 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m1EvenResidueFourInside
    m1EvenResidueFourBridgeEnd).tape
  have hleftFacing :
      s1LeftFacing 3 4 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing, binDec_zero, binDec_three_four, List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 4 1 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 4 1 a 0) i = true := by
      rw [hleftFacing]
      let R : List Bool :=
        markerWord 1 ++ (d0 ++ (d1 ++ (d1 ++ (d0 ++ lh))))
      simp only [List.append_assoc]
      change sideBit (d1pow a ++ R) i = true
      by_cases hi3 : i < 3*a
      · have hiLen : i < (d1pow a).length := by
          simpa [d1pow_length] using hi3
        rw [sideBit_append_left (d1pow a) R i hiLen]
        exact sideBit_d1pow_true a i hi3
      · have hiN_bound : i < 3*a+1 := by simpa [N] using hi
        have hieq : i = 3*a := by omega
        subst i
        have hlen : (d1pow a).length = 3*a := by simp [d1pow_length]
        rw [sideBit_append_right (d1pow a) R (3*a) (by simpa [hlen])]
        simp [R, markerWord, sideBit, d1pow_length]
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 4 1 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m1EvenResidueFourBridge_input_match a b h
  have hBridge := bridgeAt T1 hN m1EvenResidueFourInside
    m1EvenResidueFourBridgeStart m1EvenResidueFourBridgeEnd 53 rfl
    m1EvenResidueFourBridge_exact m1EvenResidueFourBridge_heads hmatch
  have hBridge' :
      run tm2 53 ⟨3,hN,T1⟩ = some ⟨4,hN+5,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m1EvenResidueFourInside
          m1EvenResidueFourBridgeEnd = (⟨4,hN+5,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m1EvenResidueFourBridgeEnd]
      · simp [frameAt_head,m1EvenResidueFourBridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+5) (3*a) := by
    intro i hi
    let x : Int := hN+5+(i:Int)
    by_cases hi0 : i = 0
    · subst i
      have hin : m1EvenResidueFourInside ((hN+5)-hN) = true := by
        simp [m1EvenResidueFourInside]
      have hcut := m1EvenResidueFourCutTape_eq_end_inside a b h
        (hN+5) (by simpa [hN] using hin)
      have hmark :
          decide (5 ∈ m1EvenResidueFourBridgeEnd.marked) = true := by
        simp [m1EvenResidueFourBridgeEnd]
      have htrue : T2 (hN+5) = true := by
        simpa [T2,hN,m1EvenResidueFourCutTape] using hcut.trans hmark
      simpa [x] using htrue
    · have hiPos : 1 ≤ i := by omega
      have hout : m1EvenResidueFourInside (x-hN) = false := by
        simp [m1EvenResidueFourInside,x]
        omega
      have hframe : T2 x = T1 x := by
        simpa [T2] using frameAt_tape_outside T1 hN
          m1EvenResidueFourInside m1EvenResidueFourBridgeEnd x hout
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
          · have hx2 : h+2 ≤ x := by
              dsimp [x,N,hN] at *
              omega
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
                  s1Config_right_cell 3 4 1 a 0 b h 1
              rw [hpres,hsrc]
            · rw [hx3'] at hpres ⊢
              change sweptLeft N T h (h+3) = true
              have hsrc : T (h+3) = true := by
                have hcoord : h+1+2 = h+3 := by omega
                simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
                  s1Config_right_cell 3 4 1 a 0 b h 2
              rw [hpres,hsrc]
      simpa [x,T2] using hframe.trans hT1
  have hScan := E_scan T2 (hN+5) (3*a) hlinear
  have hhead : hN+5+(3*a:Int) = h+4 := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*a) ⟨4,hN+5,T2⟩ = some ⟨4,h+4,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(53+3*a)) ⟨3,h,T⟩ =
      some ⟨4,h+4,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 56+12*a = 3*N+(53+3*a) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m1EvenResidueFourCutTape,hnum] using htotal

end BB6Coverage.Agent41M1EvenResidueFour
