import M1EvenValuationBridge
import M1EvenQ4Prefix
import M1EvenQ4Suffix
import Q4RightEndpoint
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# M1-even valuation source prefix

For n=(2*q+1)*2^v, this module connects the uniform two-sided bridge
to the actual S1 encoder.  It proves the source run from the canonical
state-3 S1 configuration to the q4 cut, with exact tape and head.
The parameter q is the odd quotient and v is the 2-adic valuation.
-/

namespace BB6Coverage.Agent48M1EvenValuationSource

open BB6Coverage
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48M1EvenValuationBridge
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24Q4Endpoint

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) :=
  sideBit_append_right xs ys i hi

private theorem sideBit_replicate_true (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero =>
      omega
  | succ n ih =>
      cases i with
      | zero =>
          simp [sideBit]
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'

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
    (3*a+1+k) (by simp [d1pow_length]; omega)
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

/-- The prelude tape, viewed from the new head, has the exact regular
left word required by the uniform valuation bridge. -/
private theorem m1EvenValuationPreludeLeftAt
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
  have hT1 : ∀ k : Nat,
      T1 (hN-(k:Int)) =
        sideBit ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) k := by
    intro k
    by_cases hk : k=0
    · subst k
      have hblank := sweptLeft_leftmost N0 T h
      simpa [T1,hN,N0] using hblank
    · have hpres := sweptLeft_preserves_left N0 T h
        (hN-(k:Int)) (by dsimp [hN,N0]; omega)
      have hsrc := m1EvenValuationSourceLeftAt len q v a b h k hq
      simpa [T1,hN,N0] using hpres.trans hsrc
  by_cases hi0 : i=0
  · subst i
    have hbit := hT1 0
    have hne1 : hN ≠ hN-1 := by omega
    have hne2 : hN ≠ hN-2 := by omega
    have hne3 : hN ≠ hN-3 := by omega
    simpa [valuationPreludeTape,m1EvenValuationPreludeLeft,
      sideBit,d0,d1pow,hne1,hne2,hne3] using hbit
  · by_cases hi123 : i=1 ∨ i=2 ∨ i=3
    · rcases hi123 with hi1 | hi2 | hi3
      · subst i
        simp [valuationPreludeTape,m1EvenValuationPreludeLeft,sideBit]
      · subst i
        simp [valuationPreludeTape,m1EvenValuationPreludeLeft,sideBit]
      · subst i
        simp [valuationPreludeTape,m1EvenValuationPreludeLeft,sideBit]
    · by_cases hi4 : i=4
      · subst i
        have hbit := hT1 4
        have hne1 : hN-4 ≠ hN-1 := by omega
        have hne2 : hN-4 ≠ hN-2 := by omega
        have hne3 : hN-4 ≠ hN-3 := by omega
        simpa [valuationPreludeTape,m1EvenValuationPreludeLeft,
          sideBit,d0,hne1,hne2,hne3] using hbit
      · have hi5 : 5≤i := by omega
        have hpres : valuationPreludeTape T1 hN (hN-(i:Int)) =
            T1 (hN-(i:Int)) := by
          simp [valuationPreludeTape]
          have hne1 : hN-(i:Int) ≠ hN-1 := by omega
          have hne2 : hN-(i:Int) ≠ hN-2 := by omega
          have hne3 : hN-(i:Int) ≠ hN-3 := by omega
          simp [hne1,hne2,hne3]
        rw [hpres,hT1]
        have hsourcePrefix :
            ([false,true] ++ d0).length = 5 := by
          simp [d0]
        have htargetPrefix :
            ([false,true,true,true,true]).length = 5 := by rfl
        have hsrc := sideBit_append_after_local
          ([false,true] ++ d0)
          (d1pow v ++ d0 ++ binDec len q ++ lh) i
          (by simp [d0]; omega)
        have htgt := sideBit_append_after_local
          ([false,true,true,true,true])
          (d1pow v ++ d0 ++ binDec len q ++ lh) i
          (by omega)
        have hsame : sideBit
            ([false,true] ++ d0 ++ d1pow v ++ d0 ++ binDec len q ++ lh) i =
          sideBit (d1pow v ++ d0 ++ binDec len q ++ lh) (i-5) := by
          simpa [List.append_assoc,d0] using hsrc
        have hsame' : sideBit
            (m1EvenValuationPreludeLeft v (binDec len q ++ lh)) i =
          sideBit (d1pow v ++ d0 ++ binDec len q ++ lh) (i-5) := by
          simpa [m1EvenValuationPreludeLeft,List.append_assoc] using htgt
        exact hsame.trans hsame'.symm

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
  simpa [s1PhysicalRight] using
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
        rw [sideBit_append_left (d1pow a)
          (markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail) i hlen]
        exact sideBit_d1pow_true a i hi3
      · have hieq : i=3*a := by omega
        subst i
        have hlen : (d1pow a).length = 3*a := by simp [d1pow_length]
        rw [sideBit_append_right (d1pow a)
          (markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail) (3*a)
          (by simpa [hlen])]
        simp [markerWord,sideBit]
    have hcell' : T (h-((i:Nat):Int)) =
        sideBit (d1pow a ++ markerWord 1 ++ d0 ++ d1pow v ++ d0 ++ tail) i := by
      simpa [T,henc] using hcell
    exact hcell'.trans hside
  have hright : T (h+1) = false := by
    have hc := m1EvenValuationRightCell len q v a b h 0
    simpa [s0RightFacing,sideBit] using hc
  have hSweep := counted_left_sweep N0 T h hOn hright
  have hblank : T1 hN = false := by
    have hs := sweptLeft_leftmost N0 T h
    simpa [T1,hN,N0] using hs
  have hleft1 : T1 (hN-1) = true := by
    have hpres := sweptLeft_preserves_left N0 T h (hN-1) (by dsimp [hN,N0]; omega)
    have hsrc := m1EvenValuationSourceLeftAt len q v a b h 1 hq
    simpa [T1,hN,N0,sideBit] using hpres.trans hsrc
  have hleft2 : T1 (hN-2) = false := by
    have hpres := sweptLeft_preserves_left N0 T h (hN-2) (by dsimp [hN,N0]; omega)
    have hsrc := m1EvenValuationSourceLeftAt len q v a b h 2 hq
    simpa [T1,hN,N0,sideBit,d0] using hpres.trans hsrc
  have hleft3 : T1 (hN-3) = false := by
    have hpres := sweptLeft_preserves_left N0 T h (hN-3) (by dsimp [hN,N0]; omega)
    have hsrc := m1EvenValuationSourceLeftAt len q v a b h 3 hq
    simpa [T1,hN,N0,sideBit,d0] using hpres.trans hsrc
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
          dsimp [N0] at hi
          omega
        have hs := sideBit_append_after_local
          [false,true,true,true,true]
          (d1pow v ++ d0 ++ tail) (i+1) (by simp; omega)
        change sideBit
          ([false,true,true,true,true] ++ (d1pow v ++ d0 ++ tail))
          (i+1) = true
        rw [hs]
        exact sideBit_d1pow_true v (i+1-5) htail
    simpa [P,hN,N0,T,T1] using hh.trans hbit
  have hzero1 : P (hN-((3*(v+1)+2:Nat):Int)) = false := by
    have hh := hpreLeftAll (3*(v+1)+2)
    simpa [P,hN,N0,T,T1,m1EvenValuationPreludeLeft,sideBit,d0,d1pow_length,
      List.append_assoc] using hh
  have hzero2 : P (hN-((3*(v+1)+3:Nat):Int)) = false := by
    have hh := hpreLeftAll (3*(v+1)+3)
    simpa [P,hN,m1EvenValuationPreludeLeft,sideBit,d0,d1pow_length,
      List.append_assoc] using hh
  have hR1 : T1 (hN+1) = false := by
    have hs := sweptLeft_leftmost (3*a) T h
    have hcoord : hN+1 = h-((3*a:Nat):Int) := by dsimp [hN,N0]; omega
    rw [hcoord]
    exact hs
  have hR2 : T1 (hN+2) = true := by
    by_cases ha0 : a=0
    · subst a
      have hs := sweptLeft_plus1 0 T h
      simpa [T1,hN,N0] using hs
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
      rw [hcoord,hpres]
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
      rw [hcoord,hpres]
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
      simp [P,valuationPreludeTape,x]
      have hne1 : x ≠ hN-1 := by dsimp [x]; omega
      have hne2 : x ≠ hN-2 := by dsimp [x]; omega
      have hne3 : x ≠ hN-3 := by dsimp [x]; omega
      simp [hne1,hne2,hne3]
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
            rw [hpres]
            simpa [s0RightFacing,sideBit] using hsrc
          · rw [hx3']
            have hpres := sweptLeft_preserves_right N0 T h (h+3) (by omega)
            have hsrc := m1EvenValuationRightCell len q v a b h 2
            rw [hpres]
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
