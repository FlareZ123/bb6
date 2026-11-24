import M1EvenValuationBridge
import M1EvenValuationBridgeFootprint
import M1EvenQ4Prefix
import Q4RightEndpoint
import S1Encoder
import S1CountedDrain
import CountedReset
import Lean.Elab.Tactic.Omega

/-!
# M1 valuation source and complete counted increment

For n=(2*q+1)*2^v, the first namespace connects the uniform two-sided
bridge to the actual S1 encoder and proves the exact source run to the q4
cut. The appended counted-source namespace proves the q4 suffix, reset
intermediate, and counted drain, then packages the result for every
positive n below the binary width. The parameter q is the odd quotient
and v is the 2-adic valuation.
-/

namespace BB6Coverage.Agent48M1EvenValuationSource

open BB6Coverage
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48M1EvenValuationBridge
open BB6Coverage.Agent48M1EvenValuationSweep
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24Q4Endpoint

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) :=
  sideBit_append_right xs ys i hi

private theorem sideBit_d0pow_mod (n i : Nat) (hi : i<3*n) :
    sideBit (d0pow n) i = decide (i%3=2) := by
  induction n generalizing i with
  | zero =>
      omega
  | succ n ih =>
      by_cases hsmall : i<3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h0 | h1 | h2
        · subst i
          simp [d0pow, sideBit, d0]
        · subst i
          simp [d0pow, sideBit, d0]
        · subst i
          simp [d0pow, sideBit, d0]
      · have hge : 3≤i := by omega
        have hi' : i-3 < 3*n := by omega
        have hside := sideBit_append_after_local d0 (d0pow n) i
          (by simp [d0]; omega)
        have hrec := ih (i-3) hi'
        have hmod : (i-3)%3 = i%3 := by omega
        rw [d0pow]
        calc
          sideBit (d0 ++ d0pow n) i =
              sideBit (d0pow n) (i-3) := hside
          _ = decide ((i-3)%3=2) := hrec
          _ = decide (i%3=2) := by simp [hmod]

/-- The exact state-1 input stream after the six-step prelude. -/
def m1EvenValuationPreludeLeft (v : Nat) (tail : List Bool) : List Bool :=
  [false,true,true,true,true] ++ d1pow v ++ d0 ++ tail

/-- The exact source-left stream immediately after the first counted
left sweep, anchored at its new state-3 head. -/
private theorem m1EvenValuationSourceLeftAt
    (len q v a b : Nat) (h : Int) (k : Nat)
    (hq : q < 2^len) :
    (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
      (h-((3*a+1+k:Nat):Int)) =
    sideBit ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) k := by
  let L := len+1+v
  let n := (2*q+1)*2^v
  have henc :
      s1LeftFacing L n 1 a 0 =
        (d1pow a ++ [true]) ++
          ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) := by
    simp [s1LeftFacing, L, n, binDec_zero,
      binDec_carryPrefix len q v hq, markerWord, List.append_assoc]
  have hcell := s1Config_left_cell L n 1 a 0 b h (3*a+1+k)
  have hside := sideBit_append_after_local
    (d1pow a ++ [true])
    ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh)
    (3*a+1+k) (by simp [d1pow_length])
  calc
    (s1Config L n 1 a 0 b h).tape
        (h-((3*a+1+k:Nat):Int)) =
        sideBit (s1LeftFacing L n 1 a 0) (3*a+1+k) := hcell
    _ = sideBit
        ((d1pow a ++ [true]) ++
          ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh))
        (3*a+1+k) := by rw [henc]
    _ = sideBit
        ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) k := by
          simpa [d1pow_length] using hside

private theorem m1EvenValuationSweptLeftAt
    (len q v a b : Nat) (h : Int) (i : Nat) (hq : q < 2^len) :
    sweptLeft (3*a+1) (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape h
      (h-((3*a+1:Nat):Int)-(i:Int)) =
    sideBit ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) i := by
  rw [sweptLeft_preserves_left _ _ _ _ (by omega)]
  rw [show h-((3*a+1:Nat):Int)-(i:Int) = h-((3*a+1+i:Nat):Int) by omega]
  exact m1EvenValuationSourceLeftAt len q v a b h i hq

/-- The prelude tape, viewed from the new head, has the exact regular
left word required by the uniform valuation bridge. -/
theorem m1EvenValuationPreludeLeftAt
    (len q v a b : Nat) (h : Int) (i : Nat)
    (hq : q < 2^len) :
    valuationPreludeTape
      (sweptLeft (3*a+1) (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape h)
      (h-((3*a+1:Nat):Int))
      (h-((3*a+1:Nat):Int)-(i:Int)) =
    sideBit (m1EvenValuationPreludeLeft v (binDec len q ++ lh)) i := by
  let T := (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
  let N0 : Nat := 3*a+1
  let hN : Int := h-(N0:Int)
  let T1 : Int → Bool := sweptLeft N0 T h
  change valuationPreludeTape T1 hN (hN-(i:Int)) = _
  have hT1 (k : Nat) : T1 (hN-(k:Int)) =
      sideBit ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) k :=
    m1EvenValuationSweptLeftAt len q v a b h k hq
  by_cases hi : i=1 ∨ i=2 ∨ i=3
  · rcases hi with rfl | rfl | rfl <;>
      simp [valuationPreludeTape,m1EvenValuationPreludeLeft,sideBit] <;> omega
  · have hne1 : hN-(i:Int) ≠ hN-1 := by omega
    have hne2 : hN-(i:Int) ≠ hN-2 := by omega
    have hne3 : hN-(i:Int) ≠ hN-3 := by omega
    simp only [valuationPreludeTape,hne1,hne2,hne3,ite_false]
    rw [hT1]
    by_cases hi5 : i<5
    · have hc : i=0 ∨ i=4 := by omega
      rcases hc with rfl | rfl <;>
        simp [m1EvenValuationPreludeLeft,sideBit,d0]
    · have hsrc := sideBit_append_after_local
        ([false,true] ++ d0)
        (d1pow v ++ d0 ++ binDec len q ++ lh) i (by simp [d0]; omega)
      have htgt := sideBit_append_after_local
        [false,true,true,true,true]
        (d1pow v ++ d0 ++ binDec len q ++ lh) i (by simp; omega)
      have hs : sideBit
          ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) i =
        sideBit (d1pow v ++ d0 ++ binDec len q ++ lh) (i-5) := by
          simpa [List.append_assoc,d0] using hsrc
      have ht : sideBit (m1EvenValuationPreludeLeft v (binDec len q ++ lh)) i =
        sideBit (d1pow v ++ d0 ++ binDec len q ++ lh) (i-5) := by
          simpa [m1EvenValuationPreludeLeft,List.append_assoc] using htgt
      exact hs.trans ht.symm

/-- The explicit tape at the generalized M1-even valuation q4 cut. -/
def m1EvenValuationCutTape
    (len q v a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
  let N0 := 3*a+1
  let T1 := sweptLeft N0 T h
  let hN := h-(N0:Int)
  let P := valuationPreludeTape T1 hN
  m1EvenValuationBridgeTape v P hN

private theorem m1EvenValuationRightCell
    (len q v a b : Nat) (h : Int) (i : Nat) :
    (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
      (h+1+(i:Int)) = sideBit (s0RightFacing b) i := by
  simpa [s1PhysicalRight,s0PhysicalRight] using
    (s1Config_right_cell (len+1+v) ((2*q+1)*2^v) 1 a 0 b h i)

/-- The source run from S1 to the generalized M1-even q4 cut. -/
theorem m1EvenValuation_q4_prefix_run
    (len q v a b : Nat) (h : Int) (hq : q < 2^len) :
    run tm2 (12*a+12*v+32)
      ⟨3,h,(s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape⟩ =
      some ⟨4,h+4,m1EvenValuationCutTape len q v a b h⟩ := by
  let T := (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
  let N0 : Nat := 3*a+1
  let T1 : Int → Bool := sweptLeft N0 T h
  let hN : Int := h-(N0:Int)
  let P : Int → Bool := valuationPreludeTape T1 hN
  let tail : List Bool := binDec len q ++ lh
  have henc :
      s1LeftFacing (len+1+v) ((2*q+1)*2^v) 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail := by
    simp [s1LeftFacing, binDec_zero,
      binDec_carryPrefix len q v hq, tail, List.append_assoc]
  have hOn : leftOnes T h N0 := by
    intro i hi
    have hcell := s1Config_left_cell
      (len+1+v) ((2*q+1)*2^v) 1 a 0 b h i
    have hside : sideBit
        (d1pow a ++ markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail) i = true := by
      by_cases hi3 : i < 3*a
      · have hlen : i < (d1pow a).length := by
          simpa [d1pow_length] using hi3
        have hs := sideBit_append_left (d1pow a)
          (markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail) i hlen
        simpa [List.append_assoc] using hs.trans (Agent6Q4Prefix.sideBit_d1pow_true a i hi3)
      · have hieq : i=3*a := by omega
        subst i
        have hlen : (d1pow a).length = 3*a := by simp [d1pow_length]
        have hs := sideBit_append_right (d1pow a)
          (markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail) (3*a)
          (by simp [hlen])
        simpa [hlen,List.append_assoc,markerWord,sideBit] using hs
    have hcell' : T (h-((i:Nat):Int)) =
        sideBit (d1pow a ++ markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail) i := by
      simpa [T,henc] using hcell
    exact hcell'.trans hside
  have hright : T (h+1) = false := by
    have hc := m1EvenValuationRightCell len q v a b h 0
    simpa [s0RightFacing,sideBit] using hc
  have hSweep := counted_left_sweep N0 T h hOn hright
  have hT1 (k : Nat) : T1 (hN-(k:Int)) =
      sideBit ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) k :=
    m1EvenValuationSweptLeftAt len q v a b h k hq
  have hblank : T1 hN = false := by simpa [sideBit] using hT1 0
  have hleft1 : T1 (hN-1) = true := by simpa [sideBit] using hT1 1
  have hleft2 : T1 (hN-2) = false := by simpa [sideBit,d0] using hT1 2
  have hleft3 : T1 (hN-3) = false := by simpa [sideBit,d0] using hT1 3
  have hPrelude := valuation_state3_prelude6 T1 hN hblank hleft1 hleft2 hleft3
  have hpreLeft := m1EvenValuationPreludeLeftAt len q v a b h 0 hq
  have hpreLeftAll := fun i => m1EvenValuationPreludeLeftAt len q v a b h i hq
  have hstate1Head : P hN = false := by
    have hh := hpreLeftAll 0
    simpa [P,hN,N0,T,T1,sideBit,m1EvenValuationPreludeLeft] using hh
  have hstate1Ones : state1LeftOnes P hN (3*(v+1)+1) := by
    intro i hi
    have hh := hpreLeftAll (i+1)
    have hbit : sideBit (m1EvenValuationPreludeLeft v tail) (i+1) = true := by
      by_cases hsmall : i+1<5
      · have hcases : i+1=1 ∨ i+1=2 ∨ i+1=3 ∨ i+1=4 := by omega
        rcases hcases with h1 | h2 | h3 | h4
        · have hiEq : i=0 := by omega
          subst i
          simp [m1EvenValuationPreludeLeft,sideBit]
        · have hiEq : i=1 := by omega
          subst i
          simp [m1EvenValuationPreludeLeft,sideBit]
        · have hiEq : i=2 := by omega
          subst i
          simp [m1EvenValuationPreludeLeft,sideBit]
        · have hiEq : i=3 := by omega
          subst i
          simp [m1EvenValuationPreludeLeft,sideBit]
      · have hi5 : 5≤i+1 := by omega
        have htail : i+1-5 < 3*v := by
          omega
        have hs := sideBit_append_after_local
          [false,true,true,true,true]
          (d1pow v ++ d0 ++ tail) (i+1) (by simp; omega)
        change sideBit
          ([false,true,true,true,true] ++ (d1pow v ++ d0 ++ tail))
          (i+1) = true
        rw [hs]
        change sideBit (d1pow v ++ d0 ++ tail) (i+1-5) = true
        have hside := sideBit_append_left (d1pow v) (d0 ++ tail)
          (i+1-5) (by simpa [d1pow_length] using htail)
        simpa [List.append_assoc] using hside.trans (Agent6Q4Prefix.sideBit_d1pow_true v (i+1-5) htail)
    have hcoord : hN-1-(i:Int)=hN-((i+1:Nat):Int) := by omega
    rw [hcoord]
    exact hh.trans hbit
  have hpreZero (j : Nat) (hj : j<2) :
      P (hN-((3*(v+1)+2+j:Nat):Int)) = false := by
    have hh := hpreLeftAll (3*(v+1)+2+j)
    have hlen : ([false,true,true,true,true] ++ d1pow v).length = 3*(v+1)+2 := by
      simp [d1pow_length]
      omega
    have hs := sideBit_append_after_local ([false,true,true,true,true] ++ d1pow v)
      (d0 ++ tail) (3*(v+1)+2+j) (by rw [hlen]; omega)
    have hs' : sideBit (m1EvenValuationPreludeLeft v tail) (3*(v+1)+2+j) =
        sideBit (d0 ++ tail) j := by
      rw [hlen, show 3*(v+1)+2+j-(3*(v+1)+2)=j by omega] at hs
      simpa [m1EvenValuationPreludeLeft,List.append_assoc] using hs
    have hb : sideBit (d0 ++ tail) j = false := by
      have hc : j=0 ∨ j=1 := by omega
      rcases hc with rfl | rfl <;> simp [d0,sideBit]
    exact hh.trans (hs'.trans hb)
  have hzero1 : P (hN-((3*(v+1)+2:Nat):Int)) = false := by
    simpa using hpreZero 0 (by decide)
  have hzero2 : P (hN-((3*(v+1)+3:Nat):Int)) = false := by
    rw [show 3*(v+1)+3=3*(v+1)+2+1 by omega]
    exact hpreZero 1 (by decide)
  have hR1 : T1 (hN+1) = false := by
    have hs := sweptLeft_leftmost (3*a) T h
    have hcoord : hN+1 = h-((3*a:Nat):Int) := by dsimp [hN,N0]; omega
    rw [hcoord]
    exact hs
  have hR2 : T1 (hN+2) = true := by
    by_cases ha0 : a=0
    · subst a
      have hs := sweptLeft_plus1 0 T h
      have hc : hN+2=h+1 := by dsimp [hN,N0]; omega
      rw [hc]
      exact hs
    · have hj : (3*a-1)+1 < N0 := by dsimp [N0]; omega
      have hs := sweptLeft_block N0 (3*a-1) T h hj
      have hcoord : hN+2 = h-((3*a-1:Nat):Int) := by dsimp [hN,N0]; omega
      rw [hcoord]
      exact hs
  have hR3 : T1 (hN+3) = true := by
    by_cases ha0 : a=0
    · subst a
      have hpres := sweptLeft_preserves_right N0 T h (h+2) (by omega)
      have hsrc := m1EvenValuationRightCell len q v 0 b h 1
      have hcoord : hN+3 = h+2 := by dsimp [hN,N0]; omega
      rw [hcoord]
      change sweptLeft N0 T h (h+2) = true
      rw [hpres]
      simpa [s0RightFacing,sideBit] using hsrc
    · have hj : (3*a-2)+1 < N0 := by dsimp [N0]; omega
      have hs := sweptLeft_block N0 (3*a-2) T h hj
      have hcoord : hN+3 = h-((3*a-2:Nat):Int) := by dsimp [hN,N0]; omega
      rw [hcoord]
      exact hs
  have hR4 : T1 (hN+4) = true := by
    by_cases ha0 : a=0
    · subst a
      have hpres := sweptLeft_preserves_right N0 T h (h+3) (by omega)
      have hsrc := m1EvenValuationRightCell len q v 0 b h 2
      have hcoord : hN+4 = h+3 := by dsimp [hN,N0]; omega
      rw [hcoord]
      change sweptLeft N0 T h (h+3) = true
      rw [hpres,show h+3=h+1+((2:Nat):Int) by omega]
      simpa [s0RightFacing,sideBit] using hsrc
    · have hj : (3*a-3)+1 < N0 := by dsimp [N0]; omega
      have hs := sweptLeft_block N0 (3*a-3) T h hj
      have hcoord : hN+4 = h-((3*a-3:Nat):Int) := by dsimp [hN,N0]; omega
      rw [hcoord]
      exact hs
  have hPright1 : P (hN+1) = false := by
    have hne1 : hN+1 ≠ hN-1 := by omega
    have hne2 : hN+1 ≠ hN-2 := by omega
    have hne3 : hN+1 ≠ hN-3 := by omega
    simpa [P,valuationPreludeTape,hne1,hne2,hne3] using hR1
  have hPright2 : P (hN+2) = true := by
    have hne1 : hN+2 ≠ hN-1 := by omega
    have hne2 : hN+2 ≠ hN-2 := by omega
    have hne3 : hN+2 ≠ hN-3 := by omega
    simpa [P,valuationPreludeTape,hne1,hne2,hne3] using hR2
  have hPright3 : P (hN+3) = true := by
    have hne1 : hN+3 ≠ hN-1 := by omega
    have hne2 : hN+3 ≠ hN-2 := by omega
    have hne3 : hN+3 ≠ hN-3 := by omega
    simpa [P,valuationPreludeTape,hne1,hne2,hne3] using hR3
  have hPright4 : P (hN+4) = true := by
    have hne1 : hN+4 ≠ hN-1 := by omega
    have hne2 : hN+4 ≠ hN-2 := by omega
    have hne3 : hN+4 ≠ hN-3 := by omega
    simpa [P,valuationPreludeTape,hne1,hne2,hne3] using hR4
  have hBridge := m1EvenValuationBridge_run v P hN
    hstate1Head hstate1Ones hzero1 hzero2
    hPright1 hPright2 hPright3 hPright4
  have hlinear : linearRightOnes
      (m1EvenValuationBridgeTape v P hN) (hN+5) (3*a) := by
    intro i hi
    let x : Int := hN+5+(i:Int)
    have hpresBridge :
        m1EvenValuationBridgeTape v P hN x = P x :=
      m1EvenValuationBridgeTape_preserves_right v P hN x (by
        dsimp [x]
        omega)
    have hpresPrelude : P x = T1 x := by
      have hne1 : x ≠ hN-1 := by dsimp [x]; omega
      have hne2 : x ≠ hN-2 := by dsimp [x]; omega
      have hne3 : x ≠ hN-3 := by dsimp [x]; omega
      simp [P,valuationPreludeTape,hne1,hne2,hne3]
    have hT1 : T1 x = true := by
      by_cases hx : x ≤ h
      · let j : Nat := 3*a-4-i
        have hj : j+1 < N0 := by
          dsimp [j,N0,x,hN] at *
          omega
        have hblock := sweptLeft_block N0 j T h hj
        have hcoord : x = h-(j:Int) := by
          dsimp [x,j,N0,hN]
          omega
        rw [hcoord]
        exact hblock
      · by_cases hx1 : x = h+1
        · rw [hx1]
          simpa [T1,N0] using sweptLeft_plus1 (3*a) T h
        · have hx2 : x=h+2 ∨ x=h+3 := by
            dsimp [x,N0,hN] at *
            omega
          rcases hx2 with hx2' | hx3'
          · rw [hx2']
            have hpres := sweptLeft_preserves_right N0 T h (h+2) (by omega)
            have hsrc := m1EvenValuationRightCell len q v a b h 1
            change sweptLeft N0 T h (h+2) = true
            rw [hpres]
            simpa [s0RightFacing,sideBit] using hsrc
          · rw [hx3']
            have hpres := sweptLeft_preserves_right N0 T h (h+3) (by omega)
            have hsrc := m1EvenValuationRightCell len q v a b h 2
            change sweptLeft N0 T h (h+3) = true
            rw [hpres,show h+3=h+1+((2:Nat):Int) by omega]
            simpa [s0RightFacing,sideBit] using hsrc
    calc
      m1EvenValuationBridgeTape v P hN x = P x := hpresBridge
      _ = T1 x := hpresPrelude
      _ = true := hT1
  have hScan := E_scan (m1EvenValuationBridgeTape v P hN)
    (hN+5) (3*a) hlinear
  have hhead : hN+5+(3*a:Int) = h+4 := by
    dsimp [hN,N0]
    omega
  have hscan : run tm2 (3*a)
      ⟨4,hN+5,m1EvenValuationBridgeTape v P hN⟩ =
      some ⟨4,h+4,m1EvenValuationBridgeTape v P hN⟩ := by
    simpa [hhead] using hScan
  have htotal :
      run tm2 (3*N0+(6+(12*v+23+3*a))) ⟨3,h,T⟩ =
      some ⟨4,h+4,m1EvenValuationBridgeTape v P hN⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hPrelude]
    simp only [Option.bind_some]
    rw [run_append,hBridge]
    simp only [Option.bind_some]
    exact hscan
  have hnum : 12*a+12*v+32 = 3*N0+(6+(12*v+23+3*a)) := by
    dsimp [N0]
    omega
  simpa [T,N0,T1,hN,P,m1EvenValuationCutTape,hnum] using htotal

#print axioms m1EvenValuationSourceLeftAt
#print axioms m1EvenValuationPreludeLeftAt
#print axioms m1EvenValuation_q4_prefix_run

end BB6Coverage.Agent48M1EvenValuationSource


namespace BB6Coverage.Agent48M1EvenValuationCountedSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48M1EvenValuationSource
open BB6Coverage.Agent48M1EvenValuationBridge
open BB6Coverage.Agent48M1EvenValuationSweep
open BB6Coverage.Agent24M1EvenValuationBridge
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) :=
  sideBit_append_right xs ys i hi

private theorem sideBit_d0pow_mod (n i : Nat) (hi : i<3*n) :
    sideBit (d0pow n) i = decide (i%3=2) := by
  induction n generalizing i with
  | zero =>
      omega
  | succ n ih =>
      by_cases hsmall : i<3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h0 | h1 | h2
        · subst i
          simp [d0pow, sideBit, d0]
        · subst i
          simp [d0pow, sideBit, d0]
        · subst i
          simp [d0pow, sideBit, d0]
      · have hi' : i-3 < 3*n := by omega
        have hside := sideBit_append_after_local d0 (d0pow n) i
          (by simp [d0]; omega)
        have hrec := ih (i-3) hi'
        have hmod : (i-3)%3 = i%3 := by omega
        rw [d0pow]
        calc
          sideBit (d0 ++ d0pow n) i =
              sideBit (d0pow n) (i-3) := hside
          _ = decide ((i-3)%3=2) := hrec
          _ = decide (i%3=2) := by simp [hmod]

private theorem d0pow_length (n : Nat) : (d0pow n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [d0pow,d0,ih]; omega

private theorem sideBit_m1BridgeTargetPrefix_mod
    (v i : Nat) (tail : List Bool)
    (hi : i ≤ 3*(v+1)+1) :
    sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail) i =
      decide (i%3=1) := by
  by_cases hsmall : i<5
  · have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst i
      simp [sideBit, d0, d1]
    · subst i
      simp [sideBit, d0, d1]
    · subst i
      simp [sideBit, d0, d1]
    · subst i
      simp [sideBit, d0, d1]
    · subst i
      simp [sideBit, d0, d1]
  · have hi' : i-5 < 3*v := by omega
    have hside1 := sideBit_append_after_local
      ([false,true] ++ d0) (d0pow v ++ d1 ++ tail) i
      (by simp [d0]; omega)
    have hside2 := sideBit_append_left
      (d0pow v) (d1 ++ tail) (i-5) (by simpa [d0pow_length] using hi')
    have hmod := sideBit_d0pow_mod v (i-5) hi'
    have hmod' : (i-5)%3=2 ↔ i%3=1 := by omega
    calc
      sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail) i =
          sideBit (d0pow v ++ d1 ++ tail) (i-5) := by
            simpa [List.append_assoc,d0] using hside1
      _ = sideBit (d0pow v) (i-5) := by simpa [List.append_assoc] using hside2
      _ = decide ((i-5)%3=2) := hmod
      _ = decide (i%3=1) := by simp [hmod']

private theorem sideBit_m1BridgeTargetD1
    (v j : Nat) (tail : List Bool) (hj : j<3) :
    sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail)
      (3*(v+1)+2+j) = true := by
  have hlen : ([false,true] ++ d0 ++ d0pow v).length =
      3*(v+1)+2 := by
    simp [d0,d0pow_length]
    omega
  have hside := sideBit_append_after_local
    ([false,true] ++ d0 ++ d0pow v) (d1 ++ tail)
    (3*(v+1)+2+j) (by rw [hlen]; omega)
  rw [show [false,true] ++ d0 ++ d0pow v ++ d1 ++ tail =
    ([false,true] ++ d0 ++ d0pow v) ++ (d1 ++ tail) by simp [List.append_assoc], hside, hlen]
  have hidx : 3*(v+1)+2+j-(3*(v+1)+2)=j := by omega
  rw [hidx]
  have hc : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hc with rfl | rfl | rfl <;> simp [sideBit,d1]

private theorem m1EvenValuationBridgeLeftFacing
    (v : Nat) (T : Int → Bool) (h : Int) (tail : List Bool)
    (hleft : ∀ i : Nat,
      T (h-(i:Int)) =
        sideBit ([false,true,true,true,true] ++ d1pow v ++ d0 ++ tail) i) :
    ∀ i : Nat,
      m1EvenValuationBridgeTape v T h (h-(i:Int)) =
        sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail) i := by
  let N : Nat := 3*(v+1)
  let x : Int := h-(N:Int)
  let Tleft : Int → Bool := state1SweptLeft N T h
  let Tsetup : Int → Bool := valuationSetupTape Tleft x
  let Tright : Int → Bool := state5SweptRight (v+1) Tsetup (x+1)
  have hones : state5RightOnes Tsetup (x+1) N := by
    intro j hj
    have hblock := state1SweptLeft_block N T h j hj
    have hcoord : x+1+(j:Int) = h-(N:Int)+1+(j:Int) := by
      simp [x]
    have hne0 : x+1+(j:Int) ≠ x := by omega
    have hne1 : x+1+(j:Int) ≠ x-1 := by omega
    have hne2 : x+1+(j:Int) ≠ x-2 := by omega
    have hne3 : x+1+(j:Int) ≠ x-3 := by omega
    have hsetup : Tsetup (x+1+(j:Int)) =
        Tleft (x+1+(j:Int)) := by
      simp [Tsetup,valuationSetupTape,hne0,hne1,hne2,hne3]
    change Tsetup (x+1+(j:Int)) = true
    rw [hsetup,hcoord]
    simpa [Tleft] using hblock
  have hbridge (i : Nat) :
      m1EvenValuationBridgeTape v T h (h-(i:Int)) =
        state5SweptRight (v+1) Tsetup (x+1) (h-(i:Int)) := by
    have hne : h-(i:Int) ≠ h+1 := by omega
    simp [m1EvenValuationBridgeTape,N,x,Tleft,Tsetup,Tright,
      valuationExit1Tape,hne]
  intro i
  by_cases hi : i<N
  · let j : Nat := N-1-i
    have hj : j<N := by dsimp [j]; omega
    have hcoord : h-(i:Int) = x+1+(j:Int) := by
      dsimp [x,j,N]
      omega
    have hpattern := state5SweptRight_block_pattern
      (v+1) Tsetup (x+1) j hj hones
    have hmod : j%3=1 ↔ i%3=1 := by
      dsimp [j,N]
      omega
    have hval :
        m1EvenValuationBridgeTape v T h (h-(i:Int)) =
          decide (i%3=1) := by
      calc
        m1EvenValuationBridgeTape v T h (h-(i:Int)) =
            state5SweptRight (v+1) Tsetup (x+1) (h-(i:Int)) :=
          hbridge i
        _ = state5SweptRight (v+1) Tsetup (x+1)
              (x+1+(j:Int)) := by rw [hcoord]
        _ = decide (j%3=1) := hpattern
        _ = decide (i%3=1) := by simp [hmod]
    have htarget := sideBit_m1BridgeTargetPrefix_mod v i tail (by omega)
    exact hval.trans htarget.symm
  · by_cases hiN : i=N
    · subst i
      have hpres := state5SweptRight_preserves_left
        (v+1) Tsetup (x+1) x (by omega)
      have hsetup : Tsetup x = false := by
        simp [Tsetup,valuationSetupTape] <;> omega
      have hval :
          m1EvenValuationBridgeTape v T h (h-(N:Int)) = false := by
        calc
          m1EvenValuationBridgeTape v T h (h-(N:Int)) =
              state5SweptRight (v+1) Tsetup (x+1) (h-(N:Int)) :=
            hbridge N
          _ = Tsetup x := by
            have hcoord : h-(N:Int)=x := by simp [x] <;> omega
            rw [hcoord]
            exact hpres
          _ = false := hsetup
      have htarget := sideBit_m1BridgeTargetPrefix_mod v N tail (by omega)
      have htarget' :
          sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail) N = false := by
        simpa [N] using htarget
      exact hval.trans htarget'.symm
    · by_cases hiN1 : i=N+1
      · subst i
        have hpres := state5SweptRight_preserves_left
          (v+1) Tsetup (x+1) (x-1) (by omega)
        have hsetup : Tsetup (x-1) = true := by
          simp [Tsetup,valuationSetupTape] <;> omega
        have hval :
            m1EvenValuationBridgeTape v T h (h-((N+1):Int)) = true := by
          calc
            m1EvenValuationBridgeTape v T h (h-((N+1):Int)) =
                state5SweptRight (v+1) Tsetup (x+1)
                  (h-((N+1):Int)) := hbridge (N+1)
            _ = Tsetup (x-1) := by
              have hcoord : h-((N+1):Int)=x-1 := by simp [x] <;> omega
              rw [hcoord]
              exact hpres
            _ = true := hsetup
        have htarget := sideBit_m1BridgeTargetPrefix_mod v (N+1) tail (by omega)
        have htarget' :
            sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail)
              (N+1) = true := by
          simpa [N] using htarget
        exact hval.trans htarget'.symm
      · by_cases hiN2 : i=N+2
        · subst i
          have hpres := state5SweptRight_preserves_left
            (v+1) Tsetup (x+1) (x-2) (by omega)
          have hsetup : Tsetup (x-2) = true := by
            simp [Tsetup,valuationSetupTape] <;> omega
          have hval :
              m1EvenValuationBridgeTape v T h (h-((N+2):Int)) = true := by
            calc
              m1EvenValuationBridgeTape v T h (h-((N+2):Int)) =
                  state5SweptRight (v+1) Tsetup (x+1)
                    (h-((N+2):Int)) := hbridge (N+2)
              _ = Tsetup (x-2) := by
                have hcoord : h-((N+2):Int)=x-2 := by simp [x] <;> omega
                rw [hcoord]
                exact hpres
              _ = true := hsetup
          have htarget := sideBit_m1BridgeTargetD1 v 0 tail (by omega)
          have htarget' :
              sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail)
                (N+2) = true := by
            simpa [N] using htarget
          exact hval.trans htarget'.symm
        · by_cases hiN3 : i=N+3
          · subst i
            have hpres := state5SweptRight_preserves_left
              (v+1) Tsetup (x+1) (x-3) (by omega)
            have hsetup : Tsetup (x-3) = true := by
              simp [Tsetup,valuationSetupTape] <;> omega
            have hval :
                m1EvenValuationBridgeTape v T h (h-((N+3):Int)) = true := by
              calc
                m1EvenValuationBridgeTape v T h (h-((N+3):Int)) =
                    state5SweptRight (v+1) Tsetup (x+1)
                      (h-((N+3):Int)) := hbridge (N+3)
                _ = Tsetup (x-3) := by
                  have hcoord : h-((N+3):Int)=x-3 := by simp [x] <;> omega
                  rw [hcoord]
                  exact hpres
                _ = true := hsetup
            have htarget := sideBit_m1BridgeTargetD1 v 1 tail (by omega)
            have htarget' :
                sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail)
                  (N+3) = true := by
              simpa [N] using htarget
            exact hval.trans htarget'.symm
          · have hiTail : 3*(v+1)+4 ≤ i := by
              dsimp [N] at *
              omega
            exact BB6Coverage.Agent8M1EvenValuationBridgeFootprint.m1EvenValuationBridgeLeftFacing_tail_exact_parent_type
              v T h tail i hleft hiTail

/-- The exact left-facing stream at the generalized M1 q4 cut. -/
def m1EvenValuationQ4LeftFacing (L n a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L (n-1) ++ lh

theorem m1EvenValuation_q4_leftFacing
    (len q v a b : Nat) (h : Int) (hq : q<2^len) :
    ∀ i : Nat,
      m1EvenValuationCutTape len q v a b h (h-(i:Int)) =
        sideBit
          (m1EvenValuationQ4LeftFacing
            (len+1+v) ((2*q+1)*2^v) a) i := by
  let T : Int → Bool :=
    (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
  let N0 : Nat := 3*a+1
  let T1 : Int → Bool := sweptLeft N0 T h
  let hN : Int := h-(N0:Int)
  let P : Int → Bool := valuationPreludeTape T1 hN
  have hprelude : ∀ i : Nat,
      P (hN-(i:Int)) =
        sideBit (m1EvenValuationPreludeLeft v (binDec len q ++ lh)) i := by
    intro i
    simpa [P,T1,hN,N0,T] using
      (m1EvenValuationPreludeLeftAt len q v a b h i hq)
  have hbridge := m1EvenValuationBridgeLeftFacing
    v P hN (binDec len q ++ lh) (by
      intro i
      simpa [m1EvenValuationPreludeLeft] using hprelude i)
  have hbin := binDec_sub_one_carryPrefix len q v hq
  have hQ :
      m1EvenValuationQ4LeftFacing
          (len+1+v) ((2*q+1)*2^v) a =
        ([true] ++ d1pow a) ++
          ([false,true] ++ d0 ++ d0pow v ++ d1 ++ binDec len q ++ lh) := by
    unfold m1EvenValuationQ4LeftFacing
    rw [hbin]
    simp [markerWord,List.append_assoc]
  intro i
  by_cases hi : i<N0
  · have hcut : m1EvenValuationCutTape len q v a b h (h-(i:Int)) = true := by
      by_cases hlast : i+1=N0
      · have hcoord : h-(i:Int)=hN+1 := by
          dsimp [hN,N0]
          omega
        have hexit :
            m1EvenValuationBridgeTape v P hN (hN+1) = true := by
          simp [m1EvenValuationBridgeTape,valuationExit1Tape]
        simpa [m1EvenValuationCutTape,T,T1,hN,N0,P,hcoord] using hexit
      · have hsmall : i+1<N0 := by omega
        have hx : hN+2≤h-(i:Int) := by
          dsimp [hN,N0]
          omega
        have hbridgeRight :=
          m1EvenValuationBridgeTape_preserves_right v P hN
            (h-(i:Int)) hx
        have hpreludeCell : P (h-(i:Int)) = T1 (h-(i:Int)) := by
          have hne1 : h-(i:Int) ≠ hN-1 := by
            dsimp [hN,N0]
            omega
          have hne2 : h-(i:Int) ≠ hN-2 := by
            dsimp [hN,N0]
            omega
          have hne3 : h-(i:Int) ≠ hN-3 := by
            dsimp [hN,N0]
            omega
          simp [P,valuationPreludeTape,hne1,hne2,hne3]
        have hblock := sweptLeft_block N0 i T h (by omega)
        have hT1 : T1 (h-(i:Int)) = true := by
          simpa [T1] using hblock
        calc
          m1EvenValuationCutTape len q v a b h (h-(i:Int)) =
              m1EvenValuationBridgeTape v P hN (h-(i:Int)) := by
                rfl
          _ = P (h-(i:Int)) := hbridgeRight
          _ = T1 (h-(i:Int)) := hpreludeCell
          _ = true := hT1
    have hprefix : i < ([true] ++ d1pow a).length := by
      simp [d1pow_length,N0]
      omega
    have hprefixBit : sideBit ([true] ++ d1pow a) i = true := by
      cases i with
      | zero =>
          simp [sideBit]
      | succ j =>
          have hj : j<3*a := by omega
          simpa [sideBit] using sideBit_d1pow_true a j hj
    have hQbit :
        sideBit (m1EvenValuationQ4LeftFacing
          (len+1+v) ((2*q+1)*2^v) a) i = true := by
      rw [hQ]
      rw [sideBit_append_left ([true] ++ d1pow a)
        ([false,true] ++ d0 ++ d0pow v ++ d1 ++ binDec len q ++ lh)
        i hprefix]
      exact hprefixBit
    exact hcut.trans hQbit.symm
  · let j : Nat := i-N0
    have hcoord : h-(i:Int)=hN-(j:Int) := by
      dsimp [hN,N0,j]
      omega
    have hcut :
        m1EvenValuationCutTape len q v a b h (h-(i:Int)) =
          sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ binDec len q ++ lh) j := by
      rw [hcoord]
      simpa [m1EvenValuationCutTape,T,T1,hN,N0,P] using hbridge j
    have hQside :
        sideBit (m1EvenValuationQ4LeftFacing
          (len+1+v) ((2*q+1)*2^v) a) i =
          sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ binDec len q ++ lh) j := by
      rw [hQ]
      have hside := sideBit_append_after_local
        ([true] ++ d1pow a)
        ([false,true] ++ d0 ++ d0pow v ++ d1 ++ binDec len q ++ lh)
        i (by simp [d1pow_length,N0]; omega)
      simpa [j,N0,d1pow_length] using hside
    exact hcut.trans hQside.symm

private theorem m1EvenValuationCutTapeRightCell
    (len q v a b : Nat) (h : Int) (i : Nat) (hi : 1≤i) :
    m1EvenValuationCutTape len q v a b h (h+1+(i:Int)) =
      sideBit (s0RightFacing b) i := by
  let T : Int → Bool :=
    (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
  let N0 : Nat := 3*a+1
  let T1 : Int → Bool := sweptLeft N0 T h
  let hN : Int := h-(N0:Int)
  let P : Int → Bool := valuationPreludeTape T1 hN
  have hx : hN+2≤h+1+(i:Int) := by
    dsimp [hN,N0]
    omega
  have hbridge := m1EvenValuationBridgeTape_preserves_right
    v P hN (h+1+(i:Int)) hx
  have hprelude : P (h+1+(i:Int)) = T1 (h+1+(i:Int)) := by
    have hne1 : h+1+(i:Int) ≠ hN-1 := by
      dsimp [hN,N0]
      omega
    have hne2 : h+1+(i:Int) ≠ hN-2 := by
      dsimp [hN,N0]
      omega
    have hne3 : h+1+(i:Int) ≠ hN-3 := by
      dsimp [hN,N0]
      omega
    simp [P,valuationPreludeTape,hne1,hne2,hne3]
  have hsweep : T1 (h+1+(i:Int)) = T (h+1+(i:Int)) := by
    exact sweptLeft_preserves_right N0 T h (h+1+(i:Int)) (by omega)
  have hsource :
      T (h+1+(i:Int)) = sideBit (s0RightFacing b) i := by
    simpa [T,s1PhysicalRight,s0PhysicalRight] using
      (s1Config_right_cell (len+1+v) ((2*q+1)*2^v) 1 a 0 b h i)
  calc
    m1EvenValuationCutTape len q v a b h (h+1+(i:Int)) =
        m1EvenValuationBridgeTape v P hN (h+1+(i:Int)) := rfl
    _ = P (h+1+(i:Int)) := hbridge
    _ = T1 (h+1+(i:Int)) := hprelude
    _ = T (h+1+(i:Int)) := hsweep
    _ = sideBit (s0RightFacing b) i := hsource

private theorem m1EvenValuationCutTapeHead
    (len q v a b : Nat) (h : Int) :
    m1EvenValuationCutTape len q v a b h h = true := by
  let T : Int → Bool :=
    (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
  let N0 : Nat := 3*a+1
  let T1 : Int → Bool := sweptLeft N0 T h
  let hN : Int := h-(N0:Int)
  let P : Int → Bool := valuationPreludeTape T1 hN
  by_cases ha0 : a=0
  · subst a
    have hcoord : hN+1=h := by
      dsimp [hN,N0]
      omega
    have hexit :
        m1EvenValuationBridgeTape v P hN (hN+1) = true := by
      simp [m1EvenValuationBridgeTape,valuationExit1Tape]
    simpa [m1EvenValuationCutTape,T,T1,hN,N0,P] using hexit
  · have hx : hN+2≤h := by
      dsimp [hN,N0]
      omega
    have hbridge := m1EvenValuationBridgeTape_preserves_right v P hN h hx
    have hprelude : P h = T1 h := by
      have hne1 : h ≠ hN-1 := by dsimp [hN,N0]; omega
      have hne2 : h ≠ hN-2 := by dsimp [hN,N0]; omega
      have hne3 : h ≠ hN-3 := by dsimp [hN,N0]; omega
      simp [P,valuationPreludeTape,hne1,hne2,hne3]
    have hblock := sweptLeft_block N0 0 T h (by omega)
    have hT1 : T1 h = true := by
      simpa [T1] using hblock
    calc
      m1EvenValuationCutTape len q v a b h h =
          m1EvenValuationBridgeTape v P hN h := rfl
      _ = P h := hbridge
      _ = T1 h := hprelude
      _ = true := hT1

private theorem m1EvenValuationCutTapeRightOne
    (len q v a b : Nat) (h : Int) :
    m1EvenValuationCutTape len q v a b h (h+1) = true := by
  let T : Int → Bool :=
    (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape
  let N0 : Nat := 3*a+1
  let T1 : Int → Bool := sweptLeft N0 T h
  let hN : Int := h-(N0:Int)
  let P : Int → Bool := valuationPreludeTape T1 hN
  have hx : hN+2≤h+1 := by dsimp [hN,N0]; omega
  have hbridge := m1EvenValuationBridgeTape_preserves_right v P hN (h+1) hx
  have hprelude : P (h+1) = T1 (h+1) := by
    have hne1 : h+1 ≠ hN-1 := by dsimp [hN,N0]; omega
    have hne2 : h+1 ≠ hN-2 := by dsimp [hN,N0]; omega
    have hne3 : h+1 ≠ hN-3 := by dsimp [hN,N0]; omega
    simp [P,valuationPreludeTape,hne1,hne2,hne3]
  have hsweep := sweptLeft_plus1 (3*a) T h
  have hT1 : T1 (h+1) = true := by
    simpa [T1,N0] using hsweep
  calc
    m1EvenValuationCutTape len q v a b h (h+1) =
        m1EvenValuationBridgeTape v P hN (h+1) := rfl
    _ = P (h+1) := hbridge
    _ = T1 (h+1) := hprelude
    _ = true := hT1

theorem m1EvenValuation_q4_rightShape
    (len q v a b : Nat) (h : Int) :
    Agent8Q4Suffix.q4RightShape (m1EvenValuationCutTape len q v a b h) h b := by
  unfold Agent8Q4Suffix.q4RightShape
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst i
      simpa using m1EvenValuationCutTapeHead len q v a b h
    · subst i
      exact m1EvenValuationCutTapeRightOne len q v a b h
    · subst i
      have hc := m1EvenValuationCutTapeRightCell len q v a b h 1 (by omega)
      have hb : sideBit (s0RightFacing b) 1 = true := by
        simp [s0RightFacing,sideBit]
      rw [show h+((2:Nat):Int)=h+1+((1:Nat):Int) by omega]
      exact hc.trans hb
    · subst i
      have hc := m1EvenValuationCutTapeRightCell len q v a b h 2 (by omega)
      have hb : sideBit (s0RightFacing b) 2 = true := by
        simp [s0RightFacing,sideBit]
      rw [show h+((3:Nat):Int)=h+1+((2:Nat):Int) by omega]
      exact hc.trans hb
    · subst i
      have hc := m1EvenValuationCutTapeRightCell len q v a b h 3 (by omega)
      have hb : sideBit (s0RightFacing b) 3 = true := by
        simp [s0RightFacing,sideBit]
      rw [show h+((4:Nat):Int)=h+1+((3:Nat):Int) by omega]
      exact hc.trans hb
  · have hc := m1EvenValuationCutTapeRightCell len q v a b h 4 (by omega)
    have hb : sideBit (s0RightFacing b) 4 = false := by
      simp [s0RightFacing,sideBit]
    rw [show h+5=h+1+((4:Nat):Int) by omega]
    exact hc.trans hb
  · have hc := m1EvenValuationCutTapeRightCell len q v a b h 5 (by omega)
    have hb : sideBit (s0RightFacing b) 5 = false := by
      simp [s0RightFacing,sideBit]
    rw [show h+6=h+1+((5:Nat):Int) by omega]
    exact hc.trans hb
  · intro i hi
    have hc := m1EvenValuationCutTapeRightCell len q v a b h (6+i) (by omega)
    have hb : sideBit (s0RightFacing b) (6+i) = true := by
      rw [s0RightFacing]
      have hside := sideBit_append_right
        [false,true,true,true,false,false] (d1pow (b+1)) (6+i) (by simp)
      have hidx : 6+i-6=i := by omega
      rw [hside]
      change sideBit (d1pow (b+1)) (6+i-6) = true
      rw [hidx]
      exact sideBit_d1pow_true (b+1) i (by omega)
    rw [show h+7+(i:Int)=h+1+((6+i:Nat):Int) by omega]
    exact hc.trans hb
  · intro i hi
    have hc := m1EvenValuationCutTapeRightCell len q v a b h
      (9+3*b+i) (by omega)
    have hlen : (s0RightFacing b).length = 9+3*b := by
      simp [s0RightFacing,d1pow_length]
      omega
    have hb : sideBit (s0RightFacing b) (9+3*b+i) = false :=
      sideBit_ge_length (s0RightFacing b) (9+3*b+i) (by omega)
    rw [show h+10+(3*b:Int)+(i:Int)=h+1+((9+3*b+i:Nat):Int) by omega]
    exact hc.trans hb

theorem m1EvenValuation_q4_farTail
    (len q v a b : Nat) (h : Int) :
    ∀ i : Nat, 9+3*b≤i →
      m1EvenValuationCutTape len q v a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hc := m1EvenValuationCutTapeRightCell len q v a b h i (by omega)
  have hlen : (s0RightFacing b).length = 9+3*b := by
    simp [s0RightFacing,d1pow_length]
    omega
  have hb : sideBit (s0RightFacing b) i = false :=
    sideBit_ge_length (s0RightFacing b) i (by omega)
  exact hc.trans hb

theorem m1EvenValuationQ4SuffixTargetLeft
    (L n a b : Nat) :
    s1LeftFacing L (n-1) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1EvenValuationQ4LeftFacing L n a).drop 1 := by
  unfold s1LeftFacing m1EvenValuationQ4LeftFacing
  rw [binDec_pow2_sub_one]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc,markerWord]

theorem m1EvenValuation_reset_prefix_source
    (len q v a b : Nat) (h : Int) (hq : q<2^len) :
    run tm2 (resetPrefixCost 1 ((2*q+1)*2^v) a b)
      ⟨3,h,(s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape⟩ =
      some (s1Config (len+1+v) (((2*q+1)*2^v)-1)
        0 (a+b+2) (2^b-1) 0 (h+5+(3*b:Int))) := by
  let T := m1EvenValuationCutTape len q v a b h
  let Q := m1EvenValuationQ4LeftFacing
    (len+1+v) ((2*q+1)*2^v) a
  have hshape : Agent8Q4Suffix.q4RightShape T h b :=
    m1EvenValuation_q4_rightShape len q v a b h
  have htail : ∀ i : Nat, 9+3*b≤i → T (h+1+(i:Int))=false :=
    m1EvenValuation_q4_farTail len q v a b h
  have hleft : ∀ i : Nat, T (h-(i:Int))=sideBit Q i := by
    intro i
    exact m1EvenValuation_q4_leftFacing len q v a b h hq i
  have happend :
      s1LeftFacing (len+1+v) (((2*q+1)*2^v)-1) 0
        (a+b+2) (2^b-1) =
        d0pow b ++ d1pow 2 ++ Q.drop 1 := by
    exact m1EvenValuationQ4SuffixTargetLeft
      (len+1+v) ((2*q+1)*2^v) a b
  have hfirst := m1EvenQ4First4_at T h hshape.1
  have hfull := q4_suffix_run_to_s1Config
    T h b (len+1+v) (((2*q+1)*2^v)-1) 0 (a+b+2) (2^b-1)
    Q hshape htail hleft happend
  have hrest :
      run tm2 (35+3*b) ⟨4,h+4,T⟩ = some
        (s1Config (len+1+v) (((2*q+1)*2^v)-1)
          0 (a+b+2) (2^b-1) 0 (h+5+(3*b:Int))) := by
    have hfull' := hfull
    rw [show 39+3*b=4+(35+3*b) by omega,run_add] at hfull'
    rw [hfirst] at hfull'
    simpa using hfull'
  have hprefix := m1EvenValuation_q4_prefix_run len q v a b h hq
  have hcomp :
      run tm2 ((12*a+12*v+32)+(35+3*b))
        ⟨3,h,(s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h).tape⟩ =
        some (s1Config (len+1+v) (((2*q+1)*2^v)-1)
          0 (a+b+2) (2^b-1) 0 (h+5+(3*b:Int))) := by
    rw [run_add,hprefix]
    simp only [Option.bind_some]
    exact hrest
  have hv := v2_of_odd_factorization ((2*q+1)*2^v) q v rfl
  have hcost :
      resetPrefixCost 1 ((2*q+1)*2^v) a b =
        (12*a+12*v+32)+(35+3*b) := by
    unfold resetPrefixCost
    rw [hv]
    omega
  rw [hcost]
  exact hcomp

theorem m1EvenValuation_counted_increment_source_factorized
    (len q v a b : Nat) (h : Int)
    (hq : q<2^len) (ha : 0<a) :
    run tm2 (proposedIncrementCost 1 ((2*q+1)*2^v) a b)
      (s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h) =
      some (s1Config (len+1+v) (((2*q+1)*2^v)-1)
        0 (a+b+2) 0 (2^b-1) (h+5+(3*b:Int))) := by
  let cfg := s1Config (len+1+v) ((2*q+1)*2^v) 1 a 0 b h
  have hprefix := m1EvenValuation_reset_prefix_source len q v a b h hq
  have hbound := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    (len+1+v) (((2*q+1)*2^v)-1) 0 (a+b+2) b
    (h+5+(3*b:Int)) cfg (resetPrefixCost 1 ((2*q+1)*2^v) a b)
    hprefix hbound
  rw [proposedIncrementCost_decomp 1 ((2*q+1)*2^v) a b]
  exact hrun

theorem m1EvenValuation_counted_increment_source
    (L n a b : Nat) (h : Int)
    (hn : 0<n) (hnlt : n<2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 1 n a b)
      (s1Config L n 1 a 0 b h) =
      some (s1Config L (n-1) 0 (a+b+2) 0 (2^b-1)
        (h+5+(3*b:Int))) := by
  obtain ⟨q,v,len,hfactor,hL,hq⟩ :=
    exists_odd_factor_bounded L n hn hnlt
  have hrun := m1EvenValuation_counted_increment_source_factorized
    len q v a b h hq ha
  simpa [hL,hfactor] using hrun

#print axioms m1EvenValuation_q4_leftFacing
#print axioms m1EvenValuation_q4_rightShape
#print axioms m1EvenValuation_reset_prefix_source
#print axioms m1EvenValuation_counted_increment_source_factorized
#print axioms m1EvenValuation_counted_increment_source

end BB6Coverage.Agent48M1EvenValuationCountedSource
