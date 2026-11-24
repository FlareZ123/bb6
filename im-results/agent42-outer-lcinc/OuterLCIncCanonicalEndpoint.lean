import OuterLCIncPostludeSource
import CountedSuffixOutput
import S1CarryOutputBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 4000000

/-!
# Canonical endpoint lemmas for the outer LC increment

The exact source run in OuterLCIncPostludeSource ends in a nested frame.
This file begins the pointwise identification of that frame with the
canonical marker-1 S1/S0 target for the authentic m=2,n=1 root branch.
All claims here remain intermediate until the complete module is compiled
and its exported axiom profile is checked.
-/

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8OuterLCInc
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime

/--
At the n=1,m=2 root branch, the outer H-run has valuation zero.  Its
left-facing output at h1 is exactly BinDec(L,0) ++ lh: the marker bridge
preserves the original BinDec(L,1) tail, and the zero-valuation bridge
changes the first d0 block to d1.
-/
theorem outerLCIncSourceT3_leftFacing_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ i : Nat,
      outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0
        (outerLCIncH1 h a 2 - (i:Int)) =
      sideBit (d1pow L ++ lh) i := by
  let T : Int → Bool := (s1Config L 1 2 a 0 b h).tape
  let h0 : Int := h-(3*a:Int)
  let h1 : Int := outerLCIncH1 h a 2
  let T2 : Int → Bool := outerLCIncSourceT2 T h a 2
  have hbin : binDec L 1 = d0 ++ d1pow (L-1) := by
    cases L with
    | zero =>
        omega
    | succ k =>
        have hk : 0 < 2^k := Nat.pow_pos (by decide)
        rw [binDec_odd k 0 (by omega)]
        simp [binDec_zero]
  have htail : binDec L 1 ++ lh =
      d0 ++ (d1pow (L-1) ++ lh) := by
    rw [hbin]
    simp [List.append_assoc]
  have hT2left : ∀ i : Nat,
      T2 (h1-(i:Int)) =
        sideBit (d0 ++ (d1pow (L-1) ++ lh)) i := by
    intro i
    have hp := outer_markerBridge_preserves_source L 1 2 a b h
      (by omega) (h1-(i:Int)) (by
        dsimp [h1,outerLCIncH1]
        omega)
    have hc := outer_s1_counter_cell L 1 2 a b h (by omega) i
    have hcoord : h1-(i:Int) =
        h-((3*a+2+5+i):Int) := by
      dsimp [h1,outerLCIncH1]
      omega
    calc
      T2 (h1-(i:Int)) = T (h1-(i:Int)) := by
        simpa [T2,T,outerLCIncSourceT2,outerLCIncSourceT1,h0] using hp
      _ = sideBit (binDec L 1 ++ lh) i := by
        rw [hcoord]
        simpa [T] using hc
      _ = sideBit (d0 ++ (d1pow (L-1) ++ lh)) i := by
        rw [htail]
  have hT3eq (i : Nat) :
      outerLCIncSourceT3 T h a 2 0 (h1-(i:Int)) =
        afterLIncBridge T2 h1 (h1-(i:Int)) := by
    change lbinDecHRunTape 0 T2 h1 (h1-(i:Int)) = _
    simp [lbinDecHRunTape,sweptLeft,sweptRightB]
  have hword : d1pow L ++ lh =
      d1 ++ (d1pow (L-1) ++ lh) := by
    cases L with
    | zero =>
        omega
    | succ k =>
        simp [d1pow,List.append_assoc]
  have hbit (i : Nat) (hi : 2 ≤ i) :
      sideBit (d0 ++ (d1pow (L-1) ++ lh)) i =
        sideBit (d1 ++ (d1pow (L-1) ++ lh)) i := by
    by_cases hsmall : i < 3
    · have hi2 : i = 2 := by omega
      subst i
      simp [sideBit,d0,d1]
    · have hd0 : d0.length ≤ i := by simp [d0]; omega
      have hd1 : d1.length ≤ i := by simp [d1]; omega
      rw [Agent6Q4Prefix.sideBit_append_right _ _ _ hd0,
        Agent6Q4Prefix.sideBit_append_right _ _ _ hd1]
      rfl
  intro i
  by_cases hi0 : i = 0
  · subst i
    have htarget : sideBit (d1pow L ++ lh) 0 = true := by
      rw [sideBit_append]
      have hlen : (d1pow L).length = 3*L := by simp [d1pow_length]
      have hlt : 0 < (d1pow L).length := by omega
      simp [hlt]
      exact sideBit_d1pow_true L 0 (by omega)
    simp only [Int.natCast_zero, Int.sub_zero]
    calc
      outerLCIncSourceT3 T h a 2 0 h1 =
          afterLIncBridge T2 h1 h1 := by simpa using hT3eq 0
      _ = true := by simp [afterLIncBridge]
      _ = sideBit (d1pow L ++ lh) 0 := htarget.symm
  · by_cases hi1 : i = 1
    · subst i
      have htarget : sideBit (d1pow L ++ lh) 1 = true := by
        rw [sideBit_append]
        have hlen : (d1pow L).length = 3*L := by simp [d1pow_length]
        have hlt : 1 < (d1pow L).length := by omega
        simp [hlt]
        exact sideBit_d1pow_true L 1 (by omega)
      calc
        outerLCIncSourceT3 T h a 2 0 (h1-1) =
            afterLIncBridge T2 h1 (h1-1) := hT3eq 1
        _ = true := by simp [afterLIncBridge]
        _ = sideBit (d1pow L ++ lh) 1 := htarget.symm
    · have hi2 : 2 ≤ i := by omega
      have hn0 : h1-(i:Int) ≠ h1-1 := by omega
      have hn1 : h1-(i:Int) ≠ h1 := by omega
      have hn2 : h1-(i:Int) ≠ h1+1 := by omega
      calc
        outerLCIncSourceT3 T h a 2 0 (h1-(i:Int)) =
            afterLIncBridge T2 h1 (h1-(i:Int)) := hT3eq i
        _ = T2 (h1-(i:Int)) := by
          simp [afterLIncBridge,hn0,hn1,hn2]
        _ = sideBit (d0 ++ (d1pow (L-1) ++ lh)) i := hT2left i
        _ = sideBit (d1 ++ (d1pow (L-1) ++ lh)) i := hbit i hi2
        _ = sideBit (d1pow L ++ lh) i := by rw [← hword]

/-- The two-step zero boundary does not alter any cell strictly left of h+5. -/
private theorem outerLCIncAfterZero_preserves_left
    (T : Int → Bool) (h : Int) (a m : Nat) (x : Int)
    (hx : x < h+5) :
    outerLCIncAfterZero T h a m x =
      outerLCIncAfterFive T h a m x := by
  have hnot : outerLCIncZeroInside (x-(h+5)) = false := by
    simp [outerLCIncZeroInside]
    omega
  simp [outerLCIncAfterZero,frameAt_tape,hnot]

/-- The five-step marker frame does not alter cells left of its start. -/
private theorem outerLCIncAfterFive_preserves_left
    (T : Int → Bool) (h : Int) (a m : Nat) (x : Int)
    (hx : x < outerLCIncH1 h a m+2) :
    outerLCIncAfterFive T h a m x = T x := by
  have hnot : outerLCIncFiveInside
      (x-(outerLCIncH1 h a m+2)) = false := by
    simp [outerLCIncFiveInside]
    omega
  simp [outerLCIncAfterFive,frameAt_tape,hnot]

/-- Exact local output of the five-step frame, at offsets 0 through 4. -/
private theorem outerLCIncAfterFive_local
    (T : Int → Bool) (h : Int) (a m k : Nat) (hk : k ≤ 4) :
    outerLCIncAfterFive T h a m
      (outerLCIncH1 h a m+2+(k:Int)) =
      if k=2 ∨ k=4 then true else false := by
  rw [outerLCIncAfterFive,frameAt_tape]
  have heq : outerLCIncH1 h a m+2+(k:Int)-(outerLCIncH1 h a m+2)=(k:Int) := by omega
  rw [heq]
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hc with h0|h1|h2|h3|h4 <;> subst k <;>
    simp [outerLCIncFiveInside,outerLCIncFiveEnd]

/--
The six cells immediately after the zero-valuation H-run are exactly
the marker-1/d0 boundary in head-facing order.
-/
private theorem outerLCIncAfterZero_m2_middleCell
    (T : Int → Bool) (h : Int) (a k : Nat) (hk : k < 6)
    (hT3right : T (outerLCIncH1 h a 2+1) = true) :
    outerLCIncAfterZero T h a 2
      (outerLCIncH1 h a 2+6-(k:Int)) =
      sideBit (markerWord 1 ++ d0) k := by
  let h1 : Int := outerLCIncH1 h a 2
  have hxleft : h1+6-(k:Int) < h+5 := by
    dsimp [h1,outerLCIncH1]
    omega
  have hpres0 := outerLCIncAfterZero_preserves_left T h a 2
    (h1+6-(k:Int)) hxleft
  by_cases hk5 : k=5
  · subst k
    have heq : h1+6-(5:Nat)=h1+1 := by omega
    rw [heq] at hpres0
    change outerLCIncAfterZero T h a 2 (h1+6-(5:Nat)) = _
    rw [heq]
    have hpres0' := hpres0
    have hpres5 := outerLCIncAfterFive_preserves_left T h a 2 (h1+1) (by omega)
    have hbridge : T (h1+1) = true := by
      simpa [h1] using hT3right
    have htarget : sideBit (markerWord 1 ++ d0) 5 = true := by
      simp [sideBit,markerWord,d0]
    calc
      outerLCIncAfterZero T h a 2 (h1+1) =
          outerLCIncAfterFive T h a 2 (h1+1) := hpres0'
      _ = T (h1+1) := hpres5
      _ = true := hbridge
      _ = sideBit (markerWord 1 ++ d0) 5 := htarget.symm
  · have hk4 : k ≤ 4 := by omega
    have hcoord :
        h1+6-(k:Int) = h1+2+((4-k : Nat):Int) := by omega
    have hlocal := outerLCIncAfterFive_local T h a 2 (4-k) (by omega)
    calc
      outerLCIncAfterZero T h a 2 (h1+6-(k:Int)) =
          outerLCIncAfterFive T h a 2 (h1+6-(k:Int)) := hpres0
      _ = outerLCIncAfterFive T h a 2 (h1+2+((4-k : Nat):Int)) := by
        rw [hcoord]
      _ = (if (4-k)=2 ∨ (4-k)=4 then true else false) := hlocal
      _ = sideBit (markerWord 1 ++ d0) k := by
        have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
        rcases hc with h0|h1|h2|h3|h4 <;> subst k <;>
          decide

/--
The left-facing tape at the pre-sweep head h+5 is
d1^(a+2) ++ markerWord(1) ++ d0 ++ d1^L ++ lh.
The E scan supplies the long d1 run, the five-step frame and H-run bridge
supply markerWord(1) ++ d0, and the zero-valuation H-run supplies d1^L ++ lh.
-/
theorem outerLCIncAfterZero_leftFacing_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ i : Nat,
      outerLCIncAfterZero
        (outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0)
        h a 2 (h+5-(i:Int)) =
      sideBit
        (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i := by
  let T : Int → Bool := (s1Config L 1 2 a 0 b h).tape
  let T3 : Int → Bool := outerLCIncSourceT3 T h a 2 0
  let h1 : Int := outerLCIncH1 h a 2
  rcases outerLCInc_s1_postlude_conditions L 1 2 a b 0 h (by omega) with
    ⟨_,hscan,_,_,_,_⟩
  have hT3right : T3 (h1+1) = true := by
    change lbinDecHRunTape 0 (outerLCIncSourceT2 T h a 2) h1 (h1+1) = true
    simp [lbinDecHRunTape,sweptLeft,sweptRightB,afterLIncBridge]
  have hprefixLen :
      (d1pow (a+2) ++ (markerWord 1 ++ d0)).length = 3*a+12 := by
    simp [d1pow_length,markerWord,d0]
    omega
  have htargetOne (i : Nat) (hi : i < 3*(a+2)) :
      sideBit (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++
        (d1pow L ++ lh))) i = true := by
    rw [sideBit_append]
    have hlen : (d1pow (a+2)).length = 3*(a+2) := by
      simp [d1pow_length]
    have hlt : i < (d1pow (a+2)).length := by omega
    simp [hlt]
    exact sideBit_d1pow_true (a+2) i hi
  have htargetMiddle (i k : Nat) (hk : k < 6)
      (hcoord : i=3*(a+2)+k) :
      sideBit (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++
        (d1pow L ++ lh))) i =
      sideBit (markerWord 1 ++ d0) k := by
    have hlen1 : (d1pow (a+2)).length = 3*(a+2) := d1pow_length (a+2)
    have hge1 : (d1pow (a+2)).length ≤ i := by rw [hlen1]; omega
    rw [Agent6Q4Prefix.sideBit_append_right _ _ _ hge1]
    have hsub : i-(d1pow (a+2)).length = k := by rw [hlen1]; omega
    rw [hsub]
    exact Agent6Q4Prefix.sideBit_append_left _ _ _ (by simpa [markerWord,d0] using hk)
  have htargetTail (i j : Nat) (hj : 3*a+12 ≤ i)
      (hcoord : i=3*a+12+j) :
      sideBit (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++
        (d1pow L ++ lh))) i =
      sideBit (d1pow L ++ lh) j := by
    have hword :
        d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)) =
        (d1pow (a+2) ++ (markerWord 1 ++ d0)) ++ (d1pow L ++ lh) := by
      simp [List.append_assoc]
    rw [hword]
    have hge : (d1pow (a+2) ++ (markerWord 1 ++ d0)).length ≤ i := by
      rw [hprefixLen]; omega
    rw [Agent6Q4Prefix.sideBit_append_right _ _ _ hge]
    have hsub : i-(d1pow (a+2) ++ (markerWord 1 ++ d0)).length = j := by
      rw [hprefixLen]; omega
    rw [hsub]
  intro i
  by_cases hi0 : i=0
  · subst i
    have hcell := outerLCIncAfterZero_cells T3 h a 2
    have htarget := htargetOne 0 (by omega)
    simpa [T3] using hcell.1.trans htarget.symm
  · by_cases hishort : i < 3*(a+2)
    · let j : Nat := 3*a+5-i
      have hj : j < 3*a+2+3 := by
        dsimp [j]
        omega
      have hcoord : h1+7+(j:Int) = h+5-(i:Int) := by
        dsimp [j,h1,outerLCIncH1]
        omega
      have hpres := outerLCIncAfterZero_preserves_left T3 h a 2
        (h+5-(i:Int)) (by omega)
      have hscanCell := hscan j hj
      rw [hcoord] at hscanCell
      calc
        outerLCIncAfterZero T3 h a 2 (h+5-(i:Int)) =
            outerLCIncAfterFive T3 h a 2 (h+5-(i:Int)) := hpres
        _ = true := hscanCell
        _ = sideBit
            (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i :=
          (htargetOne i hishort).symm
    · by_cases himid : i < 3*a+12
      · let k : Nat := i-(3*a+6)
        have hk : k<6 := by dsimp [k]; omega
        have hcoordI : i=3*(a+2)+k := by dsimp [k]; omega
        have hcoordX :
            h+5-(i:Int) = h1+6-(k:Int) := by
          dsimp [k,h1,outerLCIncH1]
          omega
        have hcell := outerLCIncAfterZero_m2_middleCell T3 h a k hk hT3right
        rw [← hcoordX] at hcell
        calc
          outerLCIncAfterZero T3 h a 2 (h+5-(i:Int)) =
              sideBit (markerWord 1 ++ d0) k := by
                simpa [T3] using hcell
          _ = sideBit
              (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i :=
            (htargetMiddle i k hk hcoordI).symm
      · let j : Nat := i-(3*a+12)
        have hj : 3*a+12 ≤ i := by omega
        have hcoordX :
            h+5-(i:Int) = h1-(j:Int) := by
          dsimp [j,h1,outerLCIncH1]
          omega
        have hpres0 := outerLCIncAfterZero_preserves_left T3 h a 2
          (h+5-(i:Int)) (by omega)
        have hpres5 := outerLCIncAfterFive_preserves_left T3 h a 2
          (h+5-(i:Int)) (by dsimp [h1,outerLCIncH1]; omega)
        have hleft := outerLCIncSourceT3_leftFacing_m2 L a b h hL j
        have htarget := htargetTail i j hj (by dsimp [j]; omega)
        calc
          outerLCIncAfterZero T3 h a 2 (h+5-(i:Int)) =
              outerLCIncAfterFive T3 h a 2 (h+5-(i:Int)) := hpres0
          _ = T3 (h+5-(i:Int)) := hpres5
          _ = sideBit (d1pow L ++ lh) j := by
            rw [hcoordX]
            simpa [T3] using hleft
          _ = sideBit
              (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i :=
            htarget.symm


/--
The counted B/F/D sweep prepends exactly d0^b to the pre-sweep left word.
The three residues select the two zero cells and preceding one in each
physical 001 block; the final one is the E-zero boundary at h+6.
-/
theorem outerLCIncAfterSweep_leftFacing_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ i : Nat,
      outerLCIncAfterSweep
        (outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0)
        h a 2 b (h+3*b+5-(i:Int)) =
      sideBit
        (d0pow b ++
          (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i := by
  let T : Int → Bool := (s1Config L 1 2 a 0 b h).tape
  let T3 : Int → Bool := outerLCIncSourceT3 T h a 2 0
  let U : Int → Bool := outerLCIncAfterZero T3 h a 2
  let H : Int := h+3*b+5
  rcases outerLCInc_s1_postlude_conditions L 1 2 a b 0 h (by omega) with
    ⟨_,_,_,hright,_,_⟩
  have hleft := outerLCIncAfterZero_leftFacing_m2 L a b h hL
  have htargetTail (i j : Nat) (hj : 3*b ≤ i)
      (hcoord : i=3*b+j) :
      sideBit
        (d0pow b ++
          (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i =
      sideBit
        (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) j := by
    rw [sideBit_append]
    have hlen : (d0pow b).length = 3*b := by
      exact d0pow_length b
    have hnot : ¬ i < (d0pow b).length := by
      rw [hlen]
      omega
    have hsub : i-(d0pow b).length = j := by
      rw [hlen]
      omega
    simp [hnot,hsub]
  intro i
  by_cases hi : i < 3*b
  · have hmod : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
    let q : Nat := i/3
    have hdiv : i=3*q+i%3 := by
      dsimp [q]
      omega
    have hq : q < b := by
      dsimp [q]
      omega
    rcases hmod with hmod0 | hmod1 | hmod2
    · let j : Nat := b-q-1
      have hj : j < b+1 := by dsimp [j]; omega
      have hblock := sweptRightB_block (b+1) U (h+7) hright j hj
      have hcoord : H-(i:Int) = h+7+3*(j:Int)+1 := by
        dsimp [H,j]
        rw [hdiv,hmod0]
        omega
      have htarget : sideBit (d0pow b) i = false := by
        rw [sideBit_d0pow_formula]
        simp [hi,hmod0]
      calc
        outerLCIncAfterSweep T3 h a 2 b (H-(i:Int)) =
            sweptRightB (b+1) U (h+7) (h+7+3*(j:Int)+1) := by
              simp [outerLCIncAfterSweep,hcoord,U]
        _ = false := hblock.2.1
        _ = sideBit
            (d0pow b ++
              (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i := by
              rw [Agent6Q4Prefix.sideBit_append_left _ _ _ (by rw [d0pow_length]; exact hi)]
              exact htarget.symm
    · let j : Nat := b-q-1
      have hj : j < b+1 := by dsimp [j]; omega
      have hblock := sweptRightB_block (b+1) U (h+7) hright j hj
      have hcoord : H-(i:Int) = h+7+3*(j:Int) := by
        dsimp [H,j]
        rw [hdiv,hmod1]
        omega
      have htarget : sideBit (d0pow b) i = false := by
        rw [sideBit_d0pow_formula]
        simp [hi,hmod1]
      calc
        outerLCIncAfterSweep T3 h a 2 b (H-(i:Int)) =
            sweptRightB (b+1) U (h+7) (h+7+3*(j:Int)) := by
              simp [outerLCIncAfterSweep,hcoord,U]
        _ = false := hblock.1
        _ = sideBit
            (d0pow b ++
              (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i := by
              rw [Agent6Q4Prefix.sideBit_append_left _ _ _ (by rw [d0pow_length]; exact hi)]
              exact htarget.symm
    · by_cases hlast : q+1=b
      · have hcoord : H-(i:Int)=h+6 := by
          dsimp [H]
          rw [hdiv,hmod2]
          omega
        have hpres := sweptRightB_preserves_left (b+1) U (h+7) (h+6) (by omega)
        have hzero := (outerLCIncAfterZero_cells T3 h a 2).2
        have hcell : outerLCIncAfterSweep T3 h a 2 b (h+6) = true := by
          change sweptRightB (b+1) U (h+7) (h+6) = true
          rw [hpres]
          exact hzero
        have htarget : sideBit (d0pow b) i = true := by
          rw [sideBit_d0pow_formula]
          simp [hi,hmod2]
        calc
          outerLCIncAfterSweep T3 h a 2 b (H-(i:Int)) = true := by
            rw [hcoord]
            exact hcell
          _ = sideBit
              (d0pow b ++
                (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i := by
              rw [Agent6Q4Prefix.sideBit_append_left _ _ _ (by rw [d0pow_length]; exact hi)]
              exact htarget.symm
      · have hq' : q+1 < b := by omega
        let j : Nat := b-q-2
        have hj : j < b+1 := by dsimp [j]; omega
        have hblock := sweptRightB_block (b+1) U (h+7) hright j hj
        have hcoord : H-(i:Int) = h+7+3*(j:Int)+2 := by
          dsimp [H,j]
          rw [hdiv,hmod2]
          omega
        have htarget : sideBit (d0pow b) i = true := by
          rw [sideBit_d0pow_formula]
          simp [hi,hmod2]
        calc
          outerLCIncAfterSweep T3 h a 2 b (H-(i:Int)) =
              sweptRightB (b+1) U (h+7) (h+7+3*(j:Int)+2) := by
                simp [outerLCIncAfterSweep,hcoord,U]
          _ = true := hblock.2.2
          _ = sideBit
              (d0pow b ++
                (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i := by
                rw [Agent6Q4Prefix.sideBit_append_left _ _ _ (by rw [d0pow_length]; exact hi)]
                exact htarget.symm
  · let j : Nat := i-3*b
    have hj : 3*b ≤ i := by omega
    have hcoord : H-(i:Int) = h+5-(j:Int) := by
      dsimp [H,j]
      omega
    have hpres : sweptRightB (b+1) U (h+7) (h+5-(j:Int)) =
        U (h+5-(j:Int)) :=
      sweptRightB_preserves_left (b+1) U (h+7) (h+5-(j:Int)) (by omega)
    have htarget := htargetTail i j hj (by dsimp [j]; omega)
    calc
      outerLCIncAfterSweep T3 h a 2 b (H-(i:Int)) =
          U (h+5-(j:Int)) := by
            simp [outerLCIncAfterSweep,hcoord,U,hpres]
      _ = sideBit
          (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) j := by
            simpa [U,T3] using hleft j
      _ = sideBit
          (d0pow b ++
            (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i :=
        htarget.symm


/-- The final tail frame lies strictly to the right of its final head. -/
private theorem outerLCIncPostludeTape_preserves_left
    (T : Int → Bool) (h : Int) (a m b : Nat) (x : Int)
    (hx : x ≤ h+3*b+5) :
    outerLCIncPostludeTape T h a m b x =
      outerLCIncAfterSweep T h a m b x := by
  have hnot : outerLCIncTailInside (x-(h+3*b+9)) = false := by
    simp [outerLCIncTailInside]
    omega
  have hframe :
      outerLCIncPostludeTape T h a m b x =
        outerLCIncAfterZeroExit T h a m b x := by
    simp [outerLCIncPostludeTape,frameAt_tape,hnot]
  have hne : x ≠ h+3*b+10 := by omega
  calc
    outerLCIncPostludeTape T h a m b x =
        outerLCIncAfterZeroExit T h a m b x := hframe
    _ = outerLCIncAfterSweep T h a m b x :=
      outerLCIncAfterZeroExit_preserves T h a m b x hne

/-- The final postlude tape has the complete left-facing word of the
canonical marker-1 S1/S0 target at its final head. -/
theorem outerLCIncPostludeTape_leftFacing_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ i : Nat,
      outerLCIncPostludeTape
        (outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0)
        h a 2 b (h+3*b+5-(i:Int)) =
      sideBit
        (d0pow b ++
          (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i := by
  let T : Int → Bool := (s1Config L 1 2 a 0 b h).tape
  let T3 : Int → Bool := outerLCIncSourceT3 T h a 2 0
  intro i
  have hleft := outerLCIncAfterSweep_leftFacing_m2 L a b h hL i
  have hpres := outerLCIncPostludeTape_preserves_left T3 h a 2 b
    (h+3*b+5-(i:Int)) (by omega)
  calc
    outerLCIncPostludeTape T3 h a 2 b (h+3*b+5-(i:Int)) =
        outerLCIncAfterSweep T3 h a 2 b (h+3*b+5-(i:Int)) := hpres
    _ = sideBit
        (d0pow b ++
          (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)))) i := by
            simpa [T3] using hleft

/-- The final tail frame writes exactly the canonical marker-1 S0 right
suffix: 011100111 followed by blank cells. -/
theorem outerLCIncPostludeTape_rightFacing_m2
    (L a b : Nat) (h : Int) :
    ∀ i : Nat,
      outerLCIncPostludeTape
        (outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0)
        h a 2 b (h+3*b+6+(i:Int)) =
      sideBit (s0RightFacing 0) i := by
  let T : Int → Bool := (s1Config L 1 2 a 0 b h).tape
  let T3 : Int → Bool := outerLCIncSourceT3 T h a 2 0
  let H : Int := h+3*b+5
  have hblank : ∀ j : Nat,
      (s1Config L 1 2 a 0 b h).tape (h+3*b+10+j) = false := by
    simpa using
      (outerLCInc_s1_right_facts L 1 2 a b h).2.2.2.2.2.2
  intro i
  by_cases hi : i < 9
  · rw [outerLCIncPostludeTape,frameAt_tape]
    have heq : h+3*(b:Int)+6+(i:Int)-(h+3*(b:Int)+9)=(i:Int)-3 := by omega
    rw [heq]
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    rcases hc with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst i <;>
      simp [outerLCIncTailInside,outerLCIncTailEnd,s0RightFacing,d1pow,d1,sideBit]
  · have hnot : outerLCIncTailInside
        ((H+1+(i:Int))-(h+3*b+9)) = false := by
      simp [outerLCIncTailInside,H]
      omega
    have hframe :
        outerLCIncPostludeTape T3 h a 2 b (H+1+(i:Int)) =
          outerLCIncAfterZeroExit T3 h a 2 b (H+1+(i:Int)) := by
      simp [outerLCIncPostludeTape,frameAt_tape,hnot]
    have hcoord :
        H+1+(i:Int) = h+3*b+10+((i-4 : Nat):Int) := by
      dsimp [H]
      omega
    have hzeroExit := outerLCIncAfterZeroExit_preserves T3 h a 2 b
      (H+1+(i:Int)) (by dsimp [H]; omega)
    have hT3blank : ∀ j : Nat, T3 (h+3*b+10+j) = false := by
      intro j
      rw [show T3 (h+3*b+10+j) = T (h+3*b+10+j) by
        apply outerLCIncSourceT3_preserves_right
        omega]
      exact hblank j
    have hswblank :=
      outerLCIncAfterSweep_blank T3 h a 2 b 0 (i-4) hT3blank
    have hlen : (s0RightFacing 0).length = 9 := by
      simp [s0RightFacing,d1pow_length]
    have htarget :
        sideBit (s0RightFacing 0) i = false :=
      BB6Coverage.Agent6Q4Prefix.sideBit_ge_length
        (s0RightFacing 0) i (by omega)
    have hH : h+3*(b:Int)+6+(i:Int)=H+1+(i:Int) := by dsimp [H]; omega
    rw [hH]
    calc
      outerLCIncPostludeTape T3 h a 2 b (H+1+(i:Int)) =
          outerLCIncAfterZeroExit T3 h a 2 b (H+1+(i:Int)) := hframe
      _ = outerLCIncAfterSweep T3 h a 2 b (H+1+(i:Int)) := hzeroExit
      _ = false := by rw [hcoord]; exact hswblank
      _ = sideBit (s0RightFacing 0) i := htarget.symm


/--
Canonical endpoint identification for the authentic m=2,n=1 branch.
The two pointwise side lemmas identify the complete left and right streams;
the existing target-counter identity then turns them into the canonical
marker-1 S1/S0 configuration.
-/
theorem outerLCIncPostludeTape_eq_s1Config_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    outerLCIncPostludeTape
        (outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0)
        h a 2 b =
      (s1Config L 0 1 (a+b+2) (2^b-1) 0 (h+3*b+5)).tape := by
  funext x
  let H : Int := h+3*b+5
  by_cases hx : x ≤ H
  · let i : Nat := Int.toNat (H-x)
    have hnat : (i:Int) = H-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord : x=H-(i:Int) := by omega
    rw [hcoord]
    have hleft := outerLCIncPostludeTape_leftFacing_m2 L a b h hL i
    have hcell :=
      s1Config_left_cell L 0 1 (a+b+2) (2^b-1) 0 H i
    have hword :
        s1LeftFacing L 0 1 (a+b+2) (2^b-1) =
          d0pow b ++
            (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) := by
      simp [s1LeftFacing,outerLCInc_target_binary_prefix,
        binDec_zero,List.append_assoc]
    rw [hword] at hcell
    exact hleft.trans hcell.symm
  · let i : Nat := Int.toNat (x-H-1)
    have hnat : (i:Int) = x-H-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord : x=H+1+(i:Int) := by omega
    rw [hcoord]
    have hright := outerLCIncPostludeTape_rightFacing_m2 L a b h i
    have hcell :=
      s1Config_right_cell L 0 1 (a+b+2) (2^b-1) 0 H i
    have hword : s1PhysicalRight 0 = s0RightFacing 0 := by
      simp [s1PhysicalRight,s0PhysicalRight]
    rw [hword] at hcell
    have hcoord' : h+3*(b:Int)+6+(i:Int)=H+1+(i:Int) := by dsimp [H]; omega
    rw [hcoord'] at hright
    exact hright.trans hcell.symm


/-- Same endpoint stated directly in the S0 input interface used by the
marker-1 q4 investigations. -/
theorem outerLCIncPostludeTape_eq_marker1S0_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    outerLCIncPostludeTape
        (outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0)
        h a 2 b =
      (s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh)
        (a+b+2) (2^b-1) 0 (h+3*b+5)).tape := by
  simpa [s1Config,binDec_zero,List.append_assoc] using
    outerLCIncPostludeTape_eq_s1Config_m2 L a b h hL


/-- The canonical root parameters satisfy the width/value bound required
by the general marker-1 S0 family. -/
theorem outerLCInc_marker1S0_inputBounds (a b : Nat) :
    0 < a+b+2 ∧ 2^b-1 < 2^(a+b+2) := by
  constructor
  · omega
  · have hpow : 2^b ≤ 2^(a+b+2) :=
      Nat.pow_le_pow_right (show 0<2 by decide) (by omega)
    have hpos : 0 < 2^b := Nat.pow_pos (by decide)
    omega


#print axioms outerLCIncSourceT3_leftFacing_m2
#print axioms outerLCIncPostludeTape_eq_s1Config_m2
#print axioms outerLCIncPostludeTape_eq_marker1S0_m2

end BB6Coverage.Agent42OuterLCInc
