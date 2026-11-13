import M0OddQ4Bridges
import Q4RightEndpoint
import Lean.Elab.Tactic.Omega

/-!
# m=0, odd n q4 reset prefix

The source reset prefix for the m=0 odd-inner-counter branch is split
into a counted left sweep of 9a moves, the fixed 27-step bridge, and an
E-state scan of 3(a-1) ones.  The cut is state 4 at the original head,
with right word q4RightFacing b.

The intended full reset prefix has cost 63+12a+3b and canonical target
S1(L,n-1,2,a+b+1,2^b-1,0,h+5+3b).  This file first formalizes the
specialized L=3,n=5 source prefix needed by the root itinerary.
-/

namespace BB6Coverage.Agent24M0OddQ4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24M0OddQ4Bridges
open BB6Coverage.Agent24Q4Endpoint

private theorem binDec_three_five :
    binDec 3 5 = d0 ++ d1 ++ d0 := by
  have h1 : binDec 3 5 = d0 ++ binDec 2 2 := by
    simpa using binDec_odd 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero]

private theorem m0OddSourceLeftAt (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 5 0 a 0 b h).tape
      (h - ((3*a+k : Nat) : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh) k := by
  have hleft :
      s1LeftFacing 3 5 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,binDec_three_five,List.append_assoc]
  have hcell := s1Config_left_cell 3 5 0 a 0 b h (3*a+k)
  have hside := sideBit_d1pow_append a (3*a+k)
    (markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [show 3*a+k-3*a = k by omega] using hcell

private theorem m0OddSweptLeftCell (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h
      (h - ((3*a : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh) k := by
  have hpres := sweptLeft_preserves_left (3*a)
    (s1Config 3 5 0 a 0 b h).tape h
    (h - ((3*a : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m0OddSourceLeftAt a b h k
  have hcoord :
      h - ((3*a : Nat) : Int) - (k : Int) =
        h - ((3*a+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- The complete [-6,3] input window of the combined bridge is produced
by the 9a-step counted left sweep from the m=0,n=5 source. -/
theorem m0OddQ4Bridge_input_match (a b : Nat) (h : Int)
    (ha : 0 < a) :
    ∀ y, m0OddQ4Bridge27Inside y = true →
      (sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h)
        (h - ((3*a : Nat) : Int) + y) =
          decide (y ∈ m0OddQ4Bridge27Start.marked) := by
  intro y hy
  have hyb : -6 ≤ y ∧ y ≤ 3 := by
    simpa [m0OddQ4Bridge27Inside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a : Nat) : Int) + y =
          h - ((3*a : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m0OddSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh) k =
          decide (y ∈ m0OddQ4Bridge27Start.marked) := by
      have hyCases : y = -6 ∨ y = -5 ∨ y = -4 ∨ y = -3 ∨
          y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h6 | h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m0OddQ4Bridge27Start,markerWord,d0,d1,lh,sideBit]
    exact hleft.trans hbits
  · have hyCases : y = 1 ∨ y = 2 ∨ y = 3 := by omega
    rcases hyCases with h1 | h2 | h3
    · subst y
      have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config 3 5 0 a 0 b h).tape h
      have hcoord :
          h - ((3*a : Nat) : Int) + 1 =
            h - ((3*a-1 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0OddQ4Bridge27Start] using hleft
    · subst y
      have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config 3 5 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a : Nat) : Int) + 2 =
            h - ((3*a-2 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0OddQ4Bridge27Start] using hblock
    · subst y
      have hblock := sweptLeft_block (3*a) (3*a-3)
        (s1Config 3 5 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a : Nat) : Int) + 3 =
            h - ((3*a-3 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0OddQ4Bridge27Start] using hblock

/-- Explicit tape at the m=0,n=5 q4 cut. -/
def m0OddQ4CutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 5 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int))
    m0OddQ4Bridge27Inside m0OddQ4Bridge27End).tape

private theorem m0OddQ4CutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m0OddQ4Bridge27Inside
      (x-(h-((3*a : Nat) : Int))) = false) :
    m0OddQ4CutTape a b h x =
      sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h x := by
  have hcut := frameAt_tape_outside
    (sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h)
    (h-((3*a : Nat):Int)) m0OddQ4Bridge27Inside
    m0OddQ4Bridge27End x hout
  simpa [m0OddQ4CutTape] using hcut

private theorem m0OddQ4CutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m0OddQ4Bridge27Inside
      (x-(h-((3*a : Nat) : Int))) = true) :
    m0OddQ4CutTape a b h x =
      decide ((x-(h-((3*a : Nat) : Int))) ∈
        m0OddQ4Bridge27End.marked) := by
  have hcut := frameAt_tape_inside
    (sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h)
    (h-((3*a : Nat):Int)) m0OddQ4Bridge27Inside
    m0OddQ4Bridge27End x hin
  simpa [m0OddQ4CutTape] using hcut

/-- Source-connected m=0,n=5 q4 prefix: 24+12a moves to state 4
at the original head. -/
theorem m0Odd_q4_prefix_run (a b : Nat) (h : Int)
    (ha : 0 < a) :
    run tm2 (24+12*a)
      ⟨3,h,(s1Config 3 5 0 a 0 b h).tape⟩ =
      some ⟨4,h,m0OddQ4CutTape a b h⟩ := by
  let T := (s1Config 3 5 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 :=
    (frameAt T1 hN m0OddQ4Bridge27Inside m0OddQ4Bridge27End).tape
  have hleftFacing :
      s1LeftFacing 3 5 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,binDec_three_five,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 5 0 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 5 0 a 0) i = true := by
      rw [hleftFacing]
      let R : List Bool :=
        markerWord 0 ++ (d0 ++ (d0 ++ (d1 ++ (d0 ++ lh))))
      change sideBit (d1pow a ++ R) i = true
      have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hi
      rw [sideBit_append_left (d1pow a) R i hiLen]
      exact sideBit_d1pow_true a i hi
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 5 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0OddQ4Bridge_input_match a b h ha
  have hBridge := m0OddQ4Bridge27At T1 hN hmatch
  have hBridge' :
      run tm2 27 ⟨3,hN,T1⟩ = some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0OddQ4Bridge27Inside m0OddQ4Bridge27End =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m0OddQ4Bridge27End]
      · simp [frameAt_head,m0OddQ4Bridge27End] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    let x : Int := hN+3+(i:Int)
    by_cases hi0 : i = 0
    · subst i
      have hin : m0OddQ4Bridge27Inside (x-hN) = true := by
        simp [x,m0OddQ4Bridge27Inside]
      have hcut := m0OddQ4CutTape_eq_end_inside a b h x hin
      have hmark :
          decide ((x-hN) ∈ m0OddQ4Bridge27End.marked) = true := by
        simp [x,m0OddQ4Bridge27End]
      simpa [T2,x,m0OddQ4CutTape] using hcut.trans hmark
    · have hout : m0OddQ4Bridge27Inside (x-hN) = false := by
        simp [x,m0OddQ4Bridge27Inside]
        omega
      have hcut := m0OddQ4CutTape_eq_swept a b h x (by
        simpa [x,hN] using hout)
      let j : Nat := 3*a-3-i
      have hj : j+1 < N := by
        dsimp [j,N]
        omega
      have hblock := sweptLeft_block N j T h hj
      have hcoord : x = h-(j:Int) := by
        dsimp [x,j,N,hN]
        omega
      have hblock' : sweptLeft N T h x = true := by
        rw [hcoord]
        exact hblock
      have hT : T2 x = true := by
        have hcut' := m0OddQ4CutTape_eq_swept a b h x (by
          simpa [hN,N] using hout)
        have hval := hcut'.trans hblock'
        simpa [T2,m0OddQ4CutTape,T,N,T1,hN] using hval
      simpa [x] using hT
  have hScan := E_scan T2 (hN+3) (3*(a-1)) hlinear
  have hhead : hN+3+(3*(a-1):Int) = h := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*(a-1)) ⟨4,hN+3,T2⟩ = some ⟨4,h,T2⟩ := by
    simpa [hhead] using hScan
  have hSweep' :
      run tm2 (3*N) ⟨3,h,T⟩ = some ⟨3,hN,T1⟩ := by
    simpa [N,hN,T1] using hSweep
  have htotal :
      run tm2 (3*N+(27+3*(a-1))) ⟨3,h,T⟩ =
        some ⟨4,h,T2⟩ := by
    rw [run_append,hSweep']
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 24+12*a = 3*N+(27+3*(a-1)) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m0OddQ4CutTape,hnum] using htotal

end BB6Coverage.Agent24M0OddQ4Prefix
