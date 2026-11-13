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
  simp [h1,h2,h3,binDec_zero,d1pow]

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
      have hN : (3*a-1)+1 = 3*a := by omega
      rw [hN] at hleft
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
  let T2 := m0OddQ4CutTape a b h
  have hleftFacing :
      s1LeftFacing 3 5 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,binDec_three_five,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 5 0 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 5 0 a 0) i = true := by
      rw [hleftFacing]
      simp only [List.append_assoc]
      have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hi
      rw [Agent6Q4Prefix.sideBit_append_left (d1pow a)
        (markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh) i hiLen]
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
      have hrel : x-(h-((3*a : Nat):Int)) = 3 := by
        dsimp [x,hN,N]
        omega
      have hin : m0OddQ4Bridge27Inside
          (x-(h-((3*a : Nat):Int))) = true := by
        change decide (-6 ≤ x-(h-((3*a : Nat):Int)) ∧
          x-(h-((3*a : Nat):Int)) ≤ 3) = true
        rw [hrel]
        decide
      have hcut := m0OddQ4CutTape_eq_end_inside a b h x hin
      have hmark :
          decide ((x-(h-((3*a : Nat):Int))) ∈
            m0OddQ4Bridge27End.marked) = true := by
        rw [hrel]
        simp [m0OddQ4Bridge27End]
      have hval := hcut.trans hmark
      simpa [T2,x] using hval
    · have hrel : x-(h-((3*a : Nat):Int)) = 3+(i:Int) := by
        dsimp [x,hN,N]
        omega
      have hout : m0OddQ4Bridge27Inside
          (x-(h-((3*a : Nat):Int))) = false := by
        change decide (-6 ≤ x-(h-((3*a : Nat):Int)) ∧
          x-(h-((3*a : Nat):Int)) ≤ 3) = false
        rw [hrel]
        simp [m0OddQ4Bridge27Inside]
        omega
      have hcut := m0OddQ4CutTape_eq_swept a b h x hout
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
      have hval := hcut.trans hblock'
      simpa [T2,x] using hval
  have hScan := E_scan T2 (hN+3) (3*(a-1)) hlinear
  have hhead : hN+3+(3*(a-1):Int) = h := by
    dsimp [hN,N]
    omega
  have hhead' : hN+3+((3*(a-1) : Nat):Int) = h := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*(a-1)) ⟨4,hN+3,T2⟩ = some ⟨4,h,T2⟩ := by
    have hScan' := hScan
    rw [hhead'] at hScan'
    exact hScan'
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


/-- The canonical left-facing word at the m=0,n=5 q4 cut. -/
def m0OddQ4LeftFacing (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec 3 4 ++ lh

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) :=
  Agent6Q4Prefix.sideBit_append_right xs ys i hi

private theorem binDec_three_four :
    binDec 3 4 = d1 ++ d1 ++ d0 := by
  have h1 : binDec 3 4 = d1 ++ binDec 2 2 := by
    simpa using binDec_even 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m0OddQ4LeftFacingPrefixTrue (a i : Nat)
    (ha : 0 < a) (hi : i ≤ 3*a-3) :
    sideBit (m0OddQ4LeftFacing a) i = true := by
  have hlist :
      m0OddQ4LeftFacing a =
        [true] ++
          (d1pow (a-1) ++
            (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh)) := by
    simp [m0OddQ4LeftFacing,List.append_assoc]
  by_cases hi0 : i = 0
  · subst i
    simp [hlist,sideBit]
  · have hpos : 1 ≤ i := by omega
    rw [hlist]
    rw [sideBit_append_after_local [true]
      (d1pow (a-1) ++ (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh))
      i (by simp; omega)]
    simp only [List.length_singleton]
    have hlen : i-1 < (d1pow (a-1)).length := by
      simp [d1pow_length]
      omega
    rw [Agent6Q4Prefix.sideBit_append_left (d1pow (a-1))
      (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh) (i-1) hlen]
    exact sideBit_d1pow_true (a-1) (i-1)
      (by simpa [d1pow_length] using hlen)

private theorem sideBit_binDec35_eq_binDec34_after2 (j : Nat)
    (hj : 2 ≤ j) :
    sideBit (d0 ++ d1 ++ d0 ++ lh) j =
      sideBit (d1 ++ d1 ++ d0 ++ lh) j := by
  by_cases hj2 : j = 2
  · subst j
    simp [d0,d1,sideBit]
  · have hj3 : 3 ≤ j := by omega
    have hs := sideBit_append_after_local d0 (d1 ++ d0 ++ lh) j
      (by simp [d0]; omega)
    have ht := sideBit_append_after_local d1 (d1 ++ d0 ++ lh) j
      (by simp [d1]; omega)
    simpa [List.append_assoc] using hs.trans ht.symm

private theorem m0OddQ4LeftFacingTail (a i : Nat)
    (ha : 0 < a) (hi : 3*a+7 ≤ i) :
    sideBit (s1LeftFacing 3 5 0 a 0) i =
      sideBit (m0OddQ4LeftFacing a) i := by
  have hsrc :
      s1LeftFacing 3 5 0 a 0 =
        (d1pow a ++ markerWord 0 ++ d0) ++
          (d0 ++ d1 ++ d0 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,binDec_three_five,List.append_assoc]
  have htgt :
      m0OddQ4LeftFacing a =
        ([true] ++ d1pow (a-1) ++ markerWord 2 ++ d0) ++
          (d1 ++ d1 ++ d0 ++ lh) := by
    simp [m0OddQ4LeftFacing,binDec_three_four,List.append_assoc]
  have hlenS : (d1pow a ++ markerWord 0 ++ d0).length = 3*a+5 := by
    simp [d1pow_length,markerWord,d0] <;> omega
  have hlenT :
      ([true] ++ d1pow (a-1) ++ markerWord 2 ++ d0).length = 3*a+5 := by
    simp [d1pow_length,markerWord,d0] <;> omega
  have hs0 := sideBit_append_after_local
    (d1pow a ++ markerWord 0 ++ d0) (d0 ++ d1 ++ d0 ++ lh) i
    (by rw [hlenS]; omega)
  have ht0 := sideBit_append_after_local
    ([true] ++ d1pow (a-1) ++ markerWord 2 ++ d0)
    (d1 ++ d1 ++ d0 ++ lh) i (by rw [hlenT]; omega)
  have hs : sideBit ((d1pow a ++ markerWord 0 ++ d0) ++
      (d0 ++ d1 ++ d0 ++ lh)) i =
      sideBit (d0 ++ d1 ++ d0 ++ lh) (i-(3*a+5)) := by
    simpa [List.append_assoc,hlenS] using hs0
  have ht : sideBit (([true] ++ d1pow (a-1) ++ markerWord 2 ++ d0) ++
      (d1 ++ d1 ++ d0 ++ lh)) i =
      sideBit (d1 ++ d1 ++ d0 ++ lh) (i-(3*a+5)) := by
    simpa [List.append_assoc,hlenT] using ht0
  rw [hsrc,htgt,hs,ht]
  have hj : 2 ≤ i-(3*a+5) := by omega
  exact sideBit_binDec35_eq_binDec34_after2 (i-(3*a+5)) hj

private theorem m0OddQ4CutTape_eq_source_left
    (a b : Nat) (h : Int) (i : Nat) (hi : 3*a+7 ≤ i) :
    m0OddQ4CutTape a b h (h-(i:Int)) =
      sideBit (s1LeftFacing 3 5 0 a 0) i := by
  let T := (s1Config 3 5 0 a 0 b h).tape
  have hout : m0OddQ4Bridge27Inside
      ((h-(i:Int))-(h-((3*a : Nat):Int))) = false := by
    simp [m0OddQ4Bridge27Inside]
    omega
  have hcut := m0OddQ4CutTape_eq_swept a b h (h-(i:Int)) hout
  have hpres := sweptLeft_preserves_left (3*a) T h
    (h-(i:Int)) (by omega)
  have hcell := s1Config_left_cell 3 5 0 a 0 b h i
  simpa [T] using hcut.trans (hpres.trans hcell)

/-- Every cell of the cut's left-facing stream is now identified. -/
theorem m0Odd_q4_prefix_leftFacing (a b : Nat) (h : Int)
    (ha : 0 < a) :
    ∀ i : Nat, m0OddQ4CutTape a b h (h-(i:Int)) =
      sideBit (m0OddQ4LeftFacing a) i := by
  intro i
  by_cases hprefix : i+3 ≤ 3*a
  · have htarget := m0OddQ4LeftFacingPrefixTrue a i ha (by omega)
    by_cases hedge : i+3 = 3*a
    · let x : Int := h-(i:Int)
      have hrel : x-(h-((3*a : Nat):Int)) = 3 := by
        dsimp [x]
        omega
      have hin : m0OddQ4Bridge27Inside
          (x-(h-((3*a : Nat):Int))) = true := by
        change decide (-6 ≤ x-(h-((3*a : Nat):Int)) ∧
          x-(h-((3*a : Nat):Int)) ≤ 3) = true
        rw [hrel]
        decide
      have hcut := m0OddQ4CutTape_eq_end_inside a b h x hin
      have hmark :
          decide ((x-(h-((3*a : Nat):Int))) ∈
            m0OddQ4Bridge27End.marked) = true := by
        rw [hrel]
        simp [m0OddQ4Bridge27End]
      have hval : m0OddQ4CutTape a b h x = true := by
        simpa [hrel] using hcut.trans hmark
      simpa [x] using hval.trans htarget.symm
    · let x : Int := h-(i:Int)
      have hrel : x-(h-((3*a : Nat):Int)) = (3*a:Int)-(i:Int) := by
        dsimp [x]
        omega
      have hout : m0OddQ4Bridge27Inside
          (x-(h-((3*a : Nat):Int))) = false := by
        change decide (-6 ≤ x-(h-((3*a : Nat):Int)) ∧
          x-(h-((3*a : Nat):Int)) ≤ 3) = false
        rw [hrel]
        simp [m0OddQ4Bridge27Inside]
        omega
      have hcut := m0OddQ4CutTape_eq_swept a b h x hout
      have hblock := sweptLeft_block (3*a) i
        (s1Config 3 5 0 a 0 b h).tape h (by omega)
      have hval : m0OddQ4CutTape a b h x = true := by
        calc
          m0OddQ4CutTape a b h x = sweptLeft (3*a)
              (s1Config 3 5 0 a 0 b h).tape h x := hcut
          _ = true := by simpa [x] using hblock
      simpa [x] using hval.trans htarget.symm
  · by_cases htail : 3*a+7 ≤ i
    · have hcut := m0OddQ4CutTape_eq_source_left a b h i htail
      exact hcut.trans (m0OddQ4LeftFacingTail a i ha htail)
    · have hbounds : 3*a-2 ≤ i ∧ i ≤ 3*a+6 := by omega
      let j : Nat := i-(3*a-2)
      have hj : j ≤ 8 := by dsimp [j]; omega
      let x : Int := h-(i:Int)
      have hrel : x-(h-((3*a : Nat):Int)) = 2-(j:Int) := by
        dsimp [x,j]
        omega
      have hin : m0OddQ4Bridge27Inside
          (x-(h-((3*a : Nat):Int))) = true := by
        change decide (-6 ≤ x-(h-((3*a : Nat):Int)) ∧
          x-(h-((3*a : Nat):Int)) ≤ 3) = true
        rw [hrel]
        have hj0 : 0 ≤ j := Nat.zero_le j
        simp [m0OddQ4Bridge27Inside]
        omega
      have hcut := m0OddQ4CutTape_eq_end_inside a b h x hin
      have htarget :
          sideBit (m0OddQ4LeftFacing a) i =
            decide ((2-(j:Int)) ∈ m0OddQ4Bridge27End.marked) := by
        have hlist :
            m0OddQ4LeftFacing a =
              ([true] ++ d1pow (a-1)) ++
                (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh) := by
          simp [m0OddQ4LeftFacing,List.append_assoc]
        rw [hlist]
        have hlenP : ([true] ++ d1pow (a-1)).length = 3*a-2 := by
          simp [d1pow_length]
          omega
        have hside := sideBit_append_after_local
          ([true] ++ d1pow (a-1))
          (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh) i
          (by rw [hlenP]; omega)
        have hside' :
            sideBit (([true] ++ d1pow (a-1)) ++
              (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh)) i =
            sideBit (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh)
              (i-(3*a-2)) := by
          simpa [hlenP] using hside
        have hidx : i-(3*a-2) = j := by dsimp [j]; omega
        rw [hidx] at hside'
        have hmark :
            sideBit (markerWord 2 ++ d0 ++ binDec 3 4 ++ lh) j =
              decide ((2-(j:Int)) ∈ m0OddQ4Bridge27End.marked) := by
          have hjCases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨
              j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
          rcases hjCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
          all_goals subst j
          all_goals simp [markerWord,d0,d1,binDec_three_four,sideBit,
            m0OddQ4Bridge27End]
        exact hside'.trans hmark
      have hval :
          m0OddQ4CutTape a b h x =
            sideBit (m0OddQ4LeftFacing a) i := by
        have hcut' :
            m0OddQ4CutTape a b h x =
              decide ((2-(j:Int)) ∈ m0OddQ4Bridge27End.marked) := by
          have hcut'' := hcut
          rw [hrel] at hcut''
          exact hcut''
        exact hcut'.trans htarget.symm
      simpa [x] using hval

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

/-- The complete right-facing word at the q4 cut is q4RightFacing b. -/
theorem m0Odd_q4_prefix_rightFacing (a b : Nat) (h : Int)
    (ha : 0 < a) :
    ∀ i : Nat, m0OddQ4CutTape a b h (h+1+(i:Int)) =
      sideBit (q4RightFacing b) i := by
  intro i
  by_cases hi0 : i=0
  · subst i
    have hout : m0OddQ4Bridge27Inside
        ((h+1)-(h-((3*a : Nat):Int))) = false := by
      simp [m0OddQ4Bridge27Inside]
      omega
    have hcut := m0OddQ4CutTape_eq_swept a b h (h+1) hout
    have hplus := sweptLeft_plus1 (3*a-1)
      (s1Config 3 5 0 a 0 b h).tape h
    have hN : (3*a-1)+1 = 3*a := by omega
    rw [hN] at hplus
    have hval : m0OddQ4CutTape a b h (h+1) = true := by
      exact hcut.trans hplus
    simpa [q4RightFacing,sideBit] using hval
  · have hi : 1 ≤ i := by omega
    have hout : m0OddQ4Bridge27Inside
        ((h+1+(i:Int))-(h-((3*a : Nat):Int))) = false := by
      simp [m0OddQ4Bridge27Inside]
      omega
    have hcut := m0OddQ4CutTape_eq_swept a b h
      (h+1+(i:Int)) hout
    have hpres := sweptLeft_preserves_right (3*a)
      (s1Config 3 5 0 a 0 b h).tape h
      (h+1+(i:Int)) (by omega)
    have hsrc :
        (s1Config 3 5 0 a 0 b h).tape (h+1+(i:Int)) =
          sideBit (s0RightFacing b) i := by
      simpa [s1PhysicalRight_source,s0RightFacing] using
        s1Config_right_cell 3 5 0 a 0 b h i
    have hside := sideBit_s0RightFacing_eq_q4RightFacing b i hi
    calc
      m0OddQ4CutTape a b h (h+1+(i:Int)) =
          sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h
            (h+1+(i:Int)) := hcut
      _ = (s1Config 3 5 0 a 0 b h).tape (h+1+(i:Int)) := hpres
      _ = sideBit (s0RightFacing b) i := hsrc
      _ = sideBit (q4RightFacing b) i := hside

private theorem sideBit_false_after_length_local
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero =>
          simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih i hi'

/-- The q4 right-shape contract follows from the exact right-facing word. -/
theorem m0Odd_q4_prefix_rightShape (a b : Nat) (h : Int)
    (ha : 0 < a) :
    Agent8Q4Suffix.q4RightShape (m0OddQ4CutTape a b h) h b := by
  unfold Agent8Q4Suffix.q4RightShape
  constructor
  · intro i hi
    have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst i
      have hleft := m0Odd_q4_prefix_leftFacing a b h ha 0
      simpa [m0OddQ4LeftFacing,sideBit] using hleft
    · subst i
      have hr := m0Odd_q4_prefix_rightFacing a b h ha 0
      simpa [q4RightFacing,sideBit] using hr
    · subst i
      have hr := m0Odd_q4_prefix_rightFacing a b h ha 1
      have hcoord : h+2 = h+1+(1:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
    · subst i
      have hr := m0Odd_q4_prefix_rightFacing a b h ha 2
      have hcoord : h+3 = h+1+(2:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
    · subst i
      have hr := m0Odd_q4_prefix_rightFacing a b h ha 3
      have hcoord : h+4 = h+1+(3:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
  · constructor
    · have hr := m0Odd_q4_prefix_rightFacing a b h ha 4
      have hcoord : h+5 = h+1+(4:Int) := by omega
      simpa [hcoord,q4RightFacing,sideBit] using hr
    · constructor
      · have hr := m0Odd_q4_prefix_rightFacing a b h ha 5
        have hcoord : h+6 = h+1+(5:Int) := by omega
        simpa [hcoord,q4RightFacing,sideBit] using hr
      · constructor
        · intro i hi
          have hr := m0Odd_q4_prefix_rightFacing a b h ha (6+i)
          have hones : sideBit (q4RightFacing b) (6+i) = true := by
            simp [q4RightFacing]
            exact sideBit_d1pow_true (b+1) i (by omega)
          have hcoord : h+7+(i:Int) = h+1+((6+i:Int)) := by omega
          simpa [hcoord] using hr.trans hones
        · intro i hi
          have hr := m0Odd_q4_prefix_rightFacing a b h ha (9+3*b+i)
          have hlen : (q4RightFacing b).length = 9+3*b := by
            simp [q4RightFacing,d1pow_length]
            omega
          have hblank := sideBit_false_after_length_local
            (q4RightFacing b) (9+3*b+i) (by omega)
          have hcoord :
              h+10+(3*b:Int)+(i:Int) =
                h+1+((9+3*b+i:Int)) := by omega
          simpa [hcoord] using hr.trans hblank

/-- Blank right exterior needed by the generic q4 suffix endpoint. -/
theorem m0Odd_q4_prefix_far_tail (a b : Nat) (h : Int)
    (ha : 0 < a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0OddQ4CutTape a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hr := m0Odd_q4_prefix_rightFacing a b h ha i
  have hlen : (q4RightFacing b).length = 9+3*b := by
    simp [q4RightFacing,d1pow_length]
    omega
  have hblank := sideBit_false_after_length_local
    (q4RightFacing b) i (by omega)
  exact hr.trans hblank

/-- Algebraic target-left identity for the m=0,n=5 branch. -/
theorem m0OddQ4SuffixTargetLeft (a b : Nat) (ha : 0 < a) :
    s1LeftFacing 3 4 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++ (m0OddQ4LeftFacing a).drop 1 := by
  unfold s1LeftFacing m0OddQ4LeftFacing
  have hbin0 := binDec_pow2_sub_one (a-1) b
  have hlen : a-1+b+2 = a+b+1 := by omega
  have hexp : a-1+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbin0
  rw [hbin]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [List.drop,List.append_assoc]

theorem m0Odd_resetPrefixCost_eq (a b : Nat) :
    resetPrefixCost 0 5 a b = 63+12*a+3*b := by
  have hv : BB6ChampionArithmetic.v2 5 = 0 := by
    simp [BB6ChampionArithmetic.v2]
  simp [resetPrefixCost,hv] <;> omega

/-- Complete source-level Rst0 prefix for the m=0,n=5 branch. -/
theorem m0Odd_reset_prefix_to_s1 (a b : Nat) (h : Int)
    (ha : 0 < a) :
    run tm2 (resetPrefixCost 0 5 a b)
      ⟨3,h,(s1Config 3 5 0 a 0 b h).tape⟩ =
      some (s1Config 3 4 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  let T := (s1Config 3 5 0 a 0 b h).tape
  have hprefix := m0Odd_q4_prefix_run a b h ha
  have hshape := m0Odd_q4_prefix_rightShape a b h ha
  have htail := m0Odd_q4_prefix_far_tail a b h ha
  have hleft := m0Odd_q4_prefix_leftFacing a b h ha
  have happend := m0OddQ4SuffixTargetLeft a b ha
  have hsuffix := q4_suffix_run_to_s1Config
    (m0OddQ4CutTape a b h) h b 3 4 2 (a+b+1) (2^b-1)
    (m0OddQ4LeftFacing a) hshape htail hleft happend
  have hsum :
      resetPrefixCost 0 5 a b = (24+12*a)+(39+3*b) := by
    rw [m0Odd_resetPrefixCost_eq]
    omega
  rw [hsum,run_append,hprefix]
  simpa using hsuffix

#print axioms m0OddQ4Bridge_input_match
#print axioms m0Odd_q4_prefix_run
#print axioms m0Odd_q4_prefix_leftFacing
#print axioms m0Odd_q4_prefix_rightFacing
#print axioms m0Odd_q4_prefix_rightShape
#print axioms m0Odd_reset_prefix_to_s1

end BB6Coverage.Agent24M0OddQ4Prefix
