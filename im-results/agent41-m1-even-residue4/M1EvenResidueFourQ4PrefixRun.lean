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
      have hcoord : (hN+5)-(h-((3*a+1:Nat):Int)) = 5 := by
        dsimp [hN,N]
        omega
      have hin : m1EvenResidueFourInside
          ((hN+5)-(h-((3*a+1:Nat):Int))) = true := by
        rw [hcoord]
        decide
      have hcut := m1EvenResidueFourCutTape_eq_end_inside a b h
        (hN+5) hin
      have hmark :
          decide (5 ∈ m1EvenResidueFourBridgeEnd.marked) = true := by
        decide
      have htrue : T2 (hN+5) = true := by
        rw [hcoord] at hcut
        simpa [T2,hN,N,T1,T,m1EvenResidueFourCutTape] using hcut.trans hmark
      simpa [x] using htrue
    · have hiPos : 1 ≤ i := by omega
      have hout : m1EvenResidueFourInside (x-hN) = false := by
        simp [m1EvenResidueFourInside,x]
        omega
      have hframe : T2 x = T1 x := by
        change (frameAt T1 hN m1EvenResidueFourInside
          m1EvenResidueFourBridgeEnd).tape x = T1 x
        exact Agent6Q4Prefix.frameAt_tape_outside T1 hN
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



private theorem m1EvenResidueFour_sweptLeft_head_eq_source (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft q T h (h-(q:Int)) = T (h-(q:Int)) := by
  induction q generalizing T h with
  | zero => simp [sweptLeft]
  | succ q ih =>
    have hcoord : h-(((q+1:Nat):Int)) = (h-1)-(q:Int) := by omega
    change sweptLeft q (holeThree T h) (h-1)
        (h-(((q+1:Nat):Int))) = T (h-(((q+1:Nat):Int)))
    rw [hcoord, ih (holeThree T h) (h-1)]
    have hne1 : (h-1)-(q:Int) ≠ h+1 := by omega
    have hne2 : (h-1)-(q:Int) ≠ h := by omega
    simp [holeThree,hne1,hne2]

private theorem m1EvenResidueFour_sweptLeft_head_plus1_false (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft (q+1) T h (h-(q:Int)) = false := by
  induction q generalizing T h with
  | zero =>
    simp [sweptLeft,holeThree] <;> omega
  | succ q ih =>
    have hcoord : h-(((q+1:Nat):Int)) = (h-1)-(q:Int) := by omega
    change sweptLeft (q+1) (holeThree T h) (h-1)
      (h-(((q+1:Nat):Int))) = false
    rw [hcoord]
    exact ih (holeThree T h) (h-1)

private theorem m1EvenResidueFour_leftSweep_one (T : Int → Bool) (h : Int)
    (ht : T h = true) :
    run tm2 1 ⟨3,h,T⟩ = some ⟨1,h+1,T⟩ := by
  change rawStep tm2 ⟨3,h,T⟩ = some ⟨1,h+1,T⟩
  simp only [rawStep,readSlot,ht]
  have he : tm2 ((3:Fin 6),true) = some ⟨true,true,1⟩ := rfl
  rw [he]
  simp only [Option.map_some,applyMove]
  apply congrArg (fun f : Int → Bool => some (Config.mk 1 (h+1) f))
  funext x
  by_cases hx : x=h <;> simp [hx,ht]

private theorem m1EvenResidueFour_leftSweep_two (T : Int → Bool) (h : Int)
    (ht : T h = true) (hr : T (h+1) = false) :
    run tm2 2 ⟨3,h,T⟩ =
      some ⟨2,h,(fun x => if x = h+1 then true else T x)⟩ := by
  rw [show 2 = 1+1 by omega,run_append,m1EvenResidueFour_leftSweep_one T h ht]
  simp only [Option.bind_some]
  change rawStep tm2 ⟨1,h+1,T⟩ =
    some ⟨2,h,(fun x => if x = h+1 then true else T x)⟩
  simp only [rawStep,readSlot,hr]
  have he : tm2 ((1:Fin 6),false) = some ⟨true,false,2⟩ := rfl
  rw [he]
  simp only [Option.map_some,applyMove]
  have hcoord : h+1+(-1) = h := by omega
  simpa [hcoord]

/-- Lower head bound for every prefix of the 3-cell grouped left sweep. -/
private theorem m1EvenResidueFour_counted_left_sweep_heads
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
    rw [show Tq = sweptLeft q T h by rfl,m1EvenResidueFour_sweptLeft_head_eq_source]
    exact hOn q hq
  have hqright : Tq (h-(q:Int)+1) = false := by
    change sweptLeft q T h (h-(q:Int)+1) = false
    by_cases hq0 : q = 0
    · rw [hq0]
      simpa [sweptLeft] using hr
    · obtain ⟨q',hq'⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [hq']
      have hfalse := m1EvenResidueFour_sweptLeft_head_plus1_false q' T h
      have hcoord : h-(((q'+1:Nat):Int))+1 = h-(q':Int) := by omega
      simpa only [hcoord] using hfalse
  have hqrun' :
      run tm2 (3*q) ⟨3,h,T⟩ =
        some ⟨3,h-(q:Int),Tq⟩ := by
    simpa [Tq] using hqrun
  rw [hkdecomp,run_add,hqrun'] at hd
  simp only [Option.bind_some] at hd
  have hrlt : r < 3 := Nat.mod_lt _ (by decide)
  have hrCases : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hrCases with hr0|hr1|hr2
  · rw [hr0] at hd
    simp [run] at hd
    subst d
    change h-(N:Int) ≤ h-(q:Int)
    omega
  · rw [hr1] at hd
    rw [m1EvenResidueFour_leftSweep_one Tq (h-(q:Int)) hqhead] at hd
    have heq := Option.some.inj hd
    subst d
    change h-(N:Int) ≤ h-(q:Int)+1
    omega
  · rw [hr2] at hd
    rw [m1EvenResidueFour_leftSweep_two Tq (h-(q:Int)) hqhead hqright] at hd
    have heq := Option.some.inj hd
    subst d
    change h-(N:Int) ≤ h-(q:Int)
    omega

private theorem m1EvenResidueFour_fRun_prefix_exists {m c n k d}
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
      · have hkEq : k=n+1 := by omega
        subst k
        exact ⟨d,h⟩

/-- Any intermediate configuration in the 53-step bridge stays above
the lower edge h-12 of its translated finite frame. -/
private theorem m1EvenResidueFour_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m1EvenResidueFourInside y = true →
      T (h+y) = decide (y ∈ m1EvenResidueFourBridgeStart.marked))
    (j : Nat) (hj : j < 53) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-12 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    m1EvenResidueFour_fRun_prefix_exists
      (k := j) m1EvenResidueFourBridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m1EvenResidueFourBridgeStart with
        | none => true
        | some f => m1EvenResidueFourInside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hkj : k < 53 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m1EvenResidueFourBridge_heads) k
      (List.mem_range.mpr hkj)
  have hbridgeFrame := bridgeAt T h m1EvenResidueFourInside
    m1EvenResidueFourBridgeStart e j rfl hexact hcheckj hmatch
  have hbridge : run tm2 j ⟨3,h,T⟩ =
      some (frameAt T h m1EvenResidueFourInside e) := by
    simpa [m1EvenResidueFourBridgeStart] using hbridgeFrame
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m1EvenResidueFourInside e :=
    (Option.some.inj hd).symm
  have hinside : m1EvenResidueFourInside e.head = true := by
    have hh := (List.all_eq_true.mp m1EvenResidueFourBridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -12 ≤ e.head := by
    simp [m1EvenResidueFourInside] at hinside
    omega
  rw [hdeq]
  simp [frameAt_head]
  omega

private theorem m1EvenResidueFour_E_scan_prefix_head
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
  cases heq
  rfl

/-- Every prefix of the base m=1,n=4 q4 prefix remains in
x ≥ h-(3*a+13), allowing the later arbitrary-tail frame lift. -/
theorem m1EvenResidueFour_q4_prefix_head_bound
    (a b : Nat) (h : Int) :
    ∀ k, k < 56+12*a → ∀ d,
      run tm2 k (s1Config 3 4 1 a 0 b h) = some d →
      h-((3*a+13:Int)) ≤ d.head := by
  let T := (s1Config 3 4 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m1EvenResidueFourCutTape a b h
  have hleft :
      s1LeftFacing 3 4 1 a 0 =
        d1pow a ++ (markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,binDec_three_four,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 4 1 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 4 1 a 0) i = true := by
      rw [hleft]
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
        simp [R,markerWord,sideBit,d1pow_length]
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 4 1 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch :
      ∀ y, m1EvenResidueFourInside y = true →
        T1 (hN+y) = decide (y ∈ m1EvenResidueFourBridgeStart.marked) := by
    intro y hy
    have hm := m1EvenResidueFourBridge_input_match a b h y hy
    simpa [T1,hN,N] using hm
  have hBridge := bridgeAt T1 hN m1EvenResidueFourInside
    m1EvenResidueFourBridgeStart m1EvenResidueFourBridgeEnd 53 rfl
    m1EvenResidueFourBridge_exact m1EvenResidueFourBridge_heads hmatch
  have hBridge' :
      run tm2 53 ⟨3,hN,T1⟩ =
        some ⟨4,hN+5,T2⟩ := by
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
      have hcoord : (hN+5)-(h-((3*a+1:Nat):Int)) = 5 := by
        dsimp [hN,N]
        omega
      have hin : m1EvenResidueFourInside
          ((hN+5)-(h-((3*a+1:Nat):Int))) = true := by
        rw [hcoord]
        decide
      have hcut := m1EvenResidueFourCutTape_eq_end_inside a b h
        (hN+5) hin
      have hmark :
          decide (5 ∈ m1EvenResidueFourBridgeEnd.marked) = true := by
        decide
      have htrue : T2 (hN+5) = true := by
        rw [hcoord] at hcut
        simpa [T2,hN,N,T1,T,m1EvenResidueFourCutTape] using hcut.trans hmark
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
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+53
  have hSweep' :
      run tm2 p1 (s1Config 3 4 1 a 0 b h) = some ⟨3,hN,T1⟩ := by
    simpa [p1,N,T,hN,T1] using hSweep
  by_cases hk1 : k < p1
  · have hlow := m1EvenResidueFour_counted_left_sweep_heads N T h hOn hright k
      (by dsimp [p1]; omega) d hd
    simp only [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j<53 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_append,hSweep'] at hd
      simp only [Option.bind_some] at hd
      have hlow := m1EvenResidueFour_bridge_prefix_lower T1 hN hmatch j hj d hd
      simp only [hN,N] at *
      omega
    · let j := k-p2
      have hj : j<3*a := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(53+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_append,hSweep'] at hd
      simp only [Option.bind_some] at hd
      rw [run_append,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := m1EvenResidueFour_E_scan_prefix_head
        T2 (hN+5) (3*a) hlinear j hj d hd
      simp only [hN,N] at *
      omega



private theorem m1EvenResidueFourCutTape_eq_source_right
    (a b : Nat) (h x : Int) (ha : 0 < a) (hx : h+2 ≤ x) :
    m1EvenResidueFourCutTape a b h x =
      (s1Config 3 4 1 a 0 b h).tape x := by
  let T := (s1Config 3 4 1 a 0 b h).tape
  have hgt : 5 < x-(h-((3*a+1 : Nat) : Int)) := by omega
  have hnot : ¬(-12 ≤ x-(h-((3*a+1 : Nat) : Int)) ∧
      x-(h-((3*a+1 : Nat) : Int)) ≤ 5) := by omega
  have hout : m1EvenResidueFourInside
      (x-(h-((3*a+1 : Nat) : Int))) = false := by
    change decide (-12 ≤ _ ∧ _ ≤ 5) = false
    exact decide_eq_false_iff_not.mpr hnot
  have hcut := m1EvenResidueFourCutTape_eq_swept a b h x hout
  have hpres := sweptLeft_preserves_right (3*a+1) T h x (by omega)
  simpa [T] using hcut.trans hpres

private theorem m1EvenResidueFour_sideBit_false_after_length
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
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

/-- The base q4 cut has the standard five-one guard, two zeros,
right unary counter, and blank suffix. -/
theorem m1EvenResidueFour_q4_prefix_rightShape
    (a b : Nat) (h : Int) (ha : 0 < a) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape
      (m1EvenResidueFourCutTape a b h) h b := by
  unfold BB6Coverage.Agent8Q4Suffix.q4RightShape
  let T := (s1Config 3 4 1 a 0 b h).tape
  constructor
  · intro i hi
    have hiCases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hiCases with h0 | h1 | h2 | h3 | h4
    all_goals subst i
    · by_cases ha1 : a=1
      · subst a
        have hc : h-(h-(4:Int)) = 4 := by omega
        have hin : m1EvenResidueFourInside
            (h-(h-(4:Int))) = true := by
          rw [hc]
          decide
        have hcut := m1EvenResidueFourCutTape_eq_end_inside 1 b h h hin
        have hmark :
            decide ((h-(h-(4:Int))) ∈
              m1EvenResidueFourBridgeEnd.marked) = true := by
          rw [hc]
          simp [m1EvenResidueFourBridgeEnd]
        simpa using hcut.trans hmark
      · have hnot : ¬(-12 ≤ h-(h-((3*a+1 : Nat) : Int)) ∧
            h-(h-((3*a+1 : Nat) : Int)) ≤ 5) := by omega
        have hout : m1EvenResidueFourInside
            (h-(h-((3*a+1 : Nat) : Int))) = false := by
          change decide (-12 ≤ _ ∧ _ ≤ 5) = false
          exact decide_eq_false_iff_not.mpr hnot
        have hcut := m1EvenResidueFourCutTape_eq_swept a b h h hout
        have hhead : sweptLeft (3*a+1) T h h = true := by
          have hs := sweptLeft_head (3*a-1) T h
          have hN : 3*a+1 = (3*a-1)+2 := by omega
          rw [← hN] at hs
          exact hs
        have hhead' : sweptLeft (3*a+1)
            (s1Config 3 4 1 a 0 b h).tape h h = true := by
          simpa [T] using hhead
        simpa [Int.add_zero] using hcut.trans hhead'
    · by_cases ha1 : a=1
      · subst a
        have hc : (h+1)-(h-(4:Int)) = 5 := by omega
        have hin : m1EvenResidueFourInside
            ((h+1)-(h-(4:Int))) = true := by
          rw [hc]
          decide
        have hcut := m1EvenResidueFourCutTape_eq_end_inside 1 b h (h+1) hin
        have hmark :
            decide (((h+1)-(h-(4:Int))) ∈
              m1EvenResidueFourBridgeEnd.marked) = true := by
          rw [hc]
          simp [m1EvenResidueFourBridgeEnd]
        simpa using hcut.trans hmark
      · have hnot : ¬(-12 ≤ (h+1)-(h-((3*a+1 : Nat) : Int)) ∧
            (h+1)-(h-((3*a+1 : Nat) : Int)) ≤ 5) := by omega
        have hout : m1EvenResidueFourInside
            ((h+1)-(h-((3*a+1 : Nat) : Int))) = false := by
          change decide (-12 ≤ _ ∧ _ ≤ 5) = false
          exact decide_eq_false_iff_not.mpr hnot
        have hcut := m1EvenResidueFourCutTape_eq_swept a b h (h+1) hout
        have hplus : sweptLeft (3*a+1) T h (h+1) = true := by
          simpa [T] using sweptLeft_plus1 (3*a) T h
        simpa [T] using hcut.trans hplus
    · have hcut := m1EvenResidueFourCutTape_eq_source_right
        a b h (h+2) ha (by omega)
      have hsrc : T (h+2) = true := by
        have hcoord : h+1+(1:Int) = h+2 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 1 a 0 b h 1
      exact hcut.trans hsrc
    · have hcut := m1EvenResidueFourCutTape_eq_source_right
        a b h (h+3) ha (by omega)
      have hsrc : T (h+3) = true := by
        have hcoord : h+1+(2:Int) = h+3 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 1 a 0 b h 2
      exact hcut.trans hsrc
    · have hcut := m1EvenResidueFourCutTape_eq_source_right
        a b h (h+4) ha (by omega)
      have hsrc : T (h+4) = true := by
        have hcoord : h+1+(3:Int) = h+4 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 1 a 0 b h 3
      exact hcut.trans hsrc
  · constructor
    · have hcut := m1EvenResidueFourCutTape_eq_source_right
        a b h (h+5) ha (by omega)
      have hsrc : T (h+5) = false := by
        have hcoord : h+1+(4:Int) = h+5 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 1 a 0 b h 4
      simpa [T] using hcut.trans hsrc
    · constructor
      · have hcut := m1EvenResidueFourCutTape_eq_source_right
          a b h (h+6) ha (by omega)
        have hsrc : T (h+6) = false := by
          have hcoord : h+1+(5:Int) = h+6 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell 3 4 1 a 0 b h 5
        simpa [T] using hcut.trans hsrc
      · constructor
        · intro i hi
          have hcut := m1EvenResidueFourCutTape_eq_source_right
            a b h (h+7+(i:Int)) ha (by omega)
          have hsrc : T (h+7+(i:Int)) =
              sideBit (s0RightFacing b) (6+i) := by
            have hcoord : h+1+(6+i:Int) = h+7+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit,s0RightFacing] using
              s1Config_right_cell 3 4 1 a 0 b h (6+i)
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
          have hcut := m1EvenResidueFourCutTape_eq_source_right
            a b h (h+10+(3*b:Int)+(i:Int)) ha (by omega)
          have hsrc : T (h+10+(3*b:Int)+(i:Int)) =
              sideBit (s0RightFacing b) (9+3*b+i) := by
            have hcoord : h+1+((9+3*b+i:Int)) =
                h+10+(3*b:Int)+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit,s0RightFacing] using
              s1Config_right_cell 3 4 1 a 0 b h (9+3*b+i)
          have hlen : (s0RightFacing b).length = 9+3*b := by
            simp [s0RightFacing,d1pow_length]
            omega
          have hblank : sideBit (s0RightFacing b) (9+3*b+i) = false :=
            m1EvenResidueFour_sideBit_false_after_length
              (s0RightFacing b) (9+3*b+i) (by omega)
          have htarget : T (h+10+(3*b:Int)+(i:Int)) = false := by
            rw [hsrc,hblank]
          exact hcut.trans htarget

/-- The cut preserves the entire blank suffix after the finite right-facing
unary counter, not merely the five-cell q4 guard. -/
theorem m1EvenResidueFour_q4_prefix_far_tail
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m1EvenResidueFourCutTape a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hcut := m1EvenResidueFourCutTape_eq_source_right a b h
    (h+1+(i:Int)) ha (by omega)
  have hsrc :
      (s1Config 3 4 1 a 0 b h).tape (h+1+(i:Int)) =
        sideBit (s0RightFacing b) i := by
    simpa [s1PhysicalRight_source,sideBit,s0RightFacing] using
      s1Config_right_cell 3 4 1 a 0 b h i
  have hlen : (s0RightFacing b).length = 9+3*b := by
    simp [s0RightFacing,d1pow_length]
    omega
  have hblank : sideBit (s0RightFacing b) i = false :=
    m1EvenResidueFour_sideBit_false_after_length
      (s0RightFacing b) i (by omega)
  calc
    m1EvenResidueFourCutTape a b h (h+1+(i:Int)) =
        (s1Config 3 4 1 a 0 b h).tape (h+1+(i:Int)) := hcut
    _ = sideBit (s0RightFacing b) i := hsrc
    _ = false := hblank



/-- Canonical left-facing word at the base m=1,n=4 q4 cut. -/
def m1EvenResidueFourQ4LeftFacing (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh

private theorem m1EvenResidueFour_sideBit_append_after_local
    (xs ys : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  exact Agent6Q4Prefix.sideBit_append_right xs ys i hi

private theorem m1EvenResidueFourQ4LeftFacingTail
    (a i : Nat) (hi : 3*a+14 ≤ i) :
    sideBit (s1LeftFacing 3 4 1 a 0) i =
      sideBit (m1EvenResidueFourQ4LeftFacing a) i := by
  let common : List Bool := lh
  let srcPrefix : List Bool :=
    d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0
  let tgtPrefix : List Bool :=
    [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d0 ++ d1
  have hsrc :
      s1LeftFacing 3 4 1 a 0 = srcPrefix ++ common := by
    simp [srcPrefix,common,s1LeftFacing,binDec_zero,
      binDec_three_four,d0,d1,List.append_assoc]
  have htgt :
      m1EvenResidueFourQ4LeftFacing a = tgtPrefix ++ common := by
    simp [tgtPrefix,common,m1EvenResidueFourQ4LeftFacing,
      d0,d1,List.append_assoc]
  by_cases hlast : i=3*a+14
  · subst i
    let srcInit : List Bool :=
      d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d1 ++ [false,false]
    let tgtInit : List Bool :=
      [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d0 ++ [true,true]
    have hsrc' : s1LeftFacing 3 4 1 a 0 = srcInit ++ [true] ++ lh := by
      simp [srcInit,s1LeftFacing,binDec_zero,binDec_three_four,
        markerWord,d0,d1,lh,List.append_assoc]
    have htgt' :
        m1EvenResidueFourQ4LeftFacing a = tgtInit ++ [true] ++ lh := by
      simp [tgtInit,m1EvenResidueFourQ4LeftFacing,
        markerWord,d0,d1,lh,List.append_assoc]
    have hlenS : srcInit.length = 3*a+14 := by
      simp [srcInit,d1pow_length,markerWord,d0,d1]
    have hlenT : tgtInit.length = 3*a+14 := by
      simp [tgtInit,d1pow_length,markerWord,d0,d1]
    have hs : sideBit (srcInit ++ ([true] ++ lh)) (3*a+14) = true := by
      rw [m1EvenResidueFour_sideBit_append_after_local
        srcInit ([true] ++ lh) (3*a+14) (by rw [hlenS]; omega)]
      simp [hlenS,sideBit]
    have ht : sideBit (tgtInit ++ ([true] ++ lh)) (3*a+14) = true := by
      rw [m1EvenResidueFour_sideBit_append_after_local
        tgtInit ([true] ++ lh) (3*a+14) (by rw [hlenT]; omega)]
      simp [hlenT,sideBit]
    rw [hsrc',htgt']
    simpa only [List.append_assoc] using hs.trans ht.symm
  · have hi' : 3*a+15 ≤ i := by omega
    have hs := m1EvenResidueFour_sideBit_append_after_local
      srcPrefix common i (by
        simp [srcPrefix,d1pow_length,markerWord,d0,d1]
        omega)
    have ht := m1EvenResidueFour_sideBit_append_after_local
      tgtPrefix common i (by
        simp [tgtPrefix,d1pow_length,markerWord,d0,d1]
        omega)
    have hlenS : srcPrefix.length = 3*a+15 := by
      simp [srcPrefix,d1pow_length,markerWord,d0,d1]
    have hlenT : tgtPrefix.length = 3*a+15 := by
      simp [tgtPrefix,d1pow_length,markerWord,d0,d1]
    rw [hsrc,htgt,hs,ht,hlenS,hlenT]

private theorem m1EvenResidueFourQ4LeftFacingPrefixTrue
    (a i : Nat) (hi : i ≤ 3*a) :
    sideBit (m1EvenResidueFourQ4LeftFacing a) i = true := by
  let P : List Bool := [true] ++ d1pow a
  let R : List Bool := markerWord 0 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh
  have hlist : m1EvenResidueFourQ4LeftFacing a = P ++ R := by
    simp [P,R,m1EvenResidueFourQ4LeftFacing,List.append_assoc]
  have hP : sideBit P i = true := by
    by_cases hi0 : i=0
    · subst i
      simp [P,sideBit]
    · have hpos : 1 ≤ i := by omega
      rw [show P = [true] ++ d1pow a by rfl]
      rw [m1EvenResidueFour_sideBit_append_after_local
        [true] (d1pow a) i (by simp; omega)]
      have hi' : i-1 < 3*a := by omega
      simpa [d1pow_length] using
        sideBit_d1pow_true a (i-1) hi'
  have hlen : P.length = 3*a+1 := by
    simp [P,d1pow_length]
  rw [hlist]
  rw [sideBit_append_left P R i (by rw [hlen]; omega)]
  exact hP

private theorem m1EvenResidueFourQ4LeftFacingBoundaryBit
    (a k : Nat) (hk1 : 1 ≤ k) (hk12 : k ≤ 12) :
    sideBit (m1EvenResidueFourQ4LeftFacing a) (3*a+1+k) =
      decide (-(k:Int) ∈ m1EvenResidueFourBridgeEnd.marked) := by
  let P : List Bool := [true] ++ d1pow a
  let R : List Bool := markerWord 0 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh
  have hlist : m1EvenResidueFourQ4LeftFacing a = P ++ R := by
    simp [P,R,m1EvenResidueFourQ4LeftFacing,List.append_assoc]
  have hlen : P.length = 3*a+1 := by simp [P,d1pow_length]
  rw [hlist]
  rw [m1EvenResidueFour_sideBit_append_after_local P R
    (3*a+1+k) (by rw [hlen]; omega)]
  rw [hlen]
  rw [show 3*a+1+k-(3*a+1)=k by omega]
  have hkCases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨
      k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 := by omega
  rcases hkCases with h1 | h2 | h3 | h4 | h5 | h6 |
      h7 | h8 | h9 | h10 | h11 | h12
  all_goals subst k
  all_goals simp [R,m1EvenResidueFourBridgeEnd,
    markerWord,d0,d1,lh,sideBit]

private theorem m1EvenResidueFourCutTape_eq_source_left
    (a b : Nat) (h : Int) (i : Nat) (hi : 3*a+14 ≤ i) :
    m1EvenResidueFourCutTape a b h (h-(i:Int)) =
      sideBit (s1LeftFacing 3 4 1 a 0) i := by
  let T := (s1Config 3 4 1 a 0 b h).tape
  have hnot : ¬(-12 ≤ (h-(i:Int))-(h-((3*a+1 : Nat) : Int)) ∧
      (h-(i:Int))-(h-((3*a+1 : Nat) : Int)) ≤ 5) := by omega
  have hout : m1EvenResidueFourInside
      ((h-(i:Int))-(h-((3*a+1 : Nat) : Int))) = false := by
    change decide (-12 ≤ _ ∧ _ ≤ 5) = false
    exact decide_eq_false_iff_not.mpr hnot
  have hcut := m1EvenResidueFourCutTape_eq_swept a b h
    (h-(i:Int)) hout
  have hpres := sweptLeft_preserves_left (3*a+1) T h
    (h-(i:Int)) (by omega)
  have hcell := s1Config_left_cell 3 4 1 a 0 b h i
  simpa [T] using hcut.trans (hpres.trans hcell)

/-- The q4 cut's complete left-facing stream is the canonical m=0
S1 source word for n=8k+3 at the base width k=0. -/
theorem m1EvenResidueFour_q4_prefix_leftFacing
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ i : Nat, m1EvenResidueFourCutTape a b h (h-(i:Int)) =
      sideBit (m1EvenResidueFourQ4LeftFacing a) i := by
  intro i
  by_cases hi0 : i=0
  · subst i
    have hshape := m1EvenResidueFour_q4_prefix_rightShape a b h ha
    have htrue : m1EvenResidueFourCutTape a b h h = true := by
      simpa using hshape.1 0 (by omega)
    simpa [m1EvenResidueFourQ4LeftFacing,sideBit] using htrue
  · by_cases hsmall : i ≤ 3*a
    · let x : Int := h-(i:Int)
      by_cases hfar : i+4 < 3*a
      · have hout : m1EvenResidueFourInside
            (x-(h-((3*a+1 : Nat) : Int))) = false := by
          simp [m1EvenResidueFourInside,x]
          omega
        have hcut := m1EvenResidueFourCutTape_eq_swept a b h x hout
        have hblock := sweptLeft_block (3*a+1) i
          (s1Config 3 4 1 a 0 b h).tape h (by omega)
        have hblock' :
            sweptLeft (3*a+1) (s1Config 3 4 1 a 0 b h).tape h x = true := by
          simpa [x] using hblock
        have hval : m1EvenResidueFourCutTape a b h x = true :=
          hcut.trans hblock'
        have htarget := m1EvenResidueFourQ4LeftFacingPrefixTrue a i hsmall
        simpa [x] using hval.trans htarget.symm
      · let x : Int := h-(i:Int)
        have hin : m1EvenResidueFourInside
            (x-(h-((3*a+1 : Nat) : Int))) = true := by
          simp [m1EvenResidueFourInside,x]
          omega
        have hcut := m1EvenResidueFourCutTape_eq_end_inside a b h x hin
        have hy : 1 ≤ (3*a+1-i) ∧ (3*a+1-i) ≤ 5 := by omega
        have hrel : x-(h-((3*a+1 : Nat) : Int)) =
            ((3*a+1-i : Nat) : Int) := by
          dsimp [x]
          omega
        have hmark :
            decide (x-(h-((3*a+1 : Nat) : Int)) ∈
              m1EvenResidueFourBridgeEnd.marked) = true := by
          rw [hrel]
          have hyCases : 3*a+1-i=1 ∨ 3*a+1-i=2 ∨
              3*a+1-i=3 ∨ 3*a+1-i=4 ∨ 3*a+1-i=5 := by omega
          rcases hyCases with h1 | h2 | h3 | h4 | h5
          · simp [h1,m1EvenResidueFourBridgeEnd]
          · simp [h2,m1EvenResidueFourBridgeEnd]
          · simp [h3,m1EvenResidueFourBridgeEnd]
          · simp [h4,m1EvenResidueFourBridgeEnd]
          · simp [h5,m1EvenResidueFourBridgeEnd]
        have hval : m1EvenResidueFourCutTape a b h x = true :=
          hcut.trans hmark
        have htarget := m1EvenResidueFourQ4LeftFacingPrefixTrue a i hsmall
        simpa [x] using hval.trans htarget.symm
    · by_cases hieq : i=3*a+1
      · subst i
        let x : Int := h-((3*a+1:Int))
        have hin : m1EvenResidueFourInside
            (x-(h-((3*a+1:Nat):Int))) = true := by
          simp [m1EvenResidueFourInside,x]
        have hcut := m1EvenResidueFourCutTape_eq_end_inside a b h x hin
        have hmark :
            decide (x-(h-((3*a+1:Nat):Int)) ∈
              m1EvenResidueFourBridgeEnd.marked) = false := by
          have hc : x-(h-((3*a+1:Nat):Int)) = 0 := by
            dsimp [x]
            omega
          rw [hc]
          simp [m1EvenResidueFourBridgeEnd]
        have hval : m1EvenResidueFourCutTape a b h x = false :=
          hcut.trans hmark
        have htarget :
            sideBit (m1EvenResidueFourQ4LeftFacing a) (3*a+1) = false := by
          let P : List Bool := [true] ++ d1pow a
          let R : List Bool := markerWord 0 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh
          have hlist : m1EvenResidueFourQ4LeftFacing a = P ++ R := by
            simp [P,R,m1EvenResidueFourQ4LeftFacing,List.append_assoc]
          have hlen : P.length = 3*a+1 := by simp [P,d1pow_length]
          rw [hlist]
          rw [m1EvenResidueFour_sideBit_append_after_local P R
            (3*a+1) (by rw [hlen]; omega)]
          simp [R,markerWord,sideBit,hlen]
        simpa [x] using hval.trans htarget.symm
      · by_cases hbound : i ≤ 3*a+13
        · let k : Nat := i-(3*a+1)
          have hk1 : 1 ≤ k := by dsimp [k]; omega
          have hk12 : k ≤ 12 := by dsimp [k]; omega
          let x : Int := h-(i:Int)
          have hrel : x-(h-((3*a+1:Nat):Int)) = -(k:Int) := by
            dsimp [x,k]
            omega
          have hin : m1EvenResidueFourInside (-(k:Int)) = true := by
            simp [m1EvenResidueFourInside]
            omega
          have hin' : m1EvenResidueFourInside
              (x-(h-((3*a+1:Nat):Int))) = true := by
            rw [hrel]
            exact hin
          have hcut := m1EvenResidueFourCutTape_eq_end_inside a b h x hin'
          have hi : i=3*a+1+k := by dsimp [k]; omega
          have htarget := m1EvenResidueFourQ4LeftFacingBoundaryBit a k hk1 hk12
          have htarget' :
              sideBit (m1EvenResidueFourQ4LeftFacing a) i =
                decide (-(k:Int) ∈ m1EvenResidueFourBridgeEnd.marked) := by
            rw [hi]
            exact htarget
          have hmark' : decide
              (x-(h-((3*a+1:Nat):Int)) ∈
                m1EvenResidueFourBridgeEnd.marked) =
                decide (-(k:Int) ∈ m1EvenResidueFourBridgeEnd.marked) := by
            rw [hrel]
          have hval :
              m1EvenResidueFourCutTape a b h x =
                sideBit (m1EvenResidueFourQ4LeftFacing a) i := by
            calc
              m1EvenResidueFourCutTape a b h x =
                  decide (x-(h-((3*a+1:Nat):Int)) ∈
                    m1EvenResidueFourBridgeEnd.marked) := hcut
              _ = decide (-(k:Int) ∈ m1EvenResidueFourBridgeEnd.marked) := hmark'
              _ = sideBit (m1EvenResidueFourQ4LeftFacing a) i := htarget'.symm
          exact hval
        · have htail := m1EvenResidueFourCutTape_eq_source_left
            a b h i (by omega)
          have hbits := m1EvenResidueFourQ4LeftFacingTail a i (by omega)
          exact htail.trans hbits

end BB6Coverage.Agent41M1EvenResidueFour
