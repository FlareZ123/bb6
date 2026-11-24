import CountedLBinDecHRun
import S1CarryOutputBridge
import Lean.Elab.Tactic.Omega

/-!
# Left-facing output of the counted L-bin-decrement H-run

A reusable word-level theorem for the original TM2 H-run.  The physical
B-sweep writes false,false,true in increasing tape order; read from the
new head this is exactly d0^n.  The three-cell boundary is d1, and the
far-left tail is unchanged.
-/

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24LBinDecHRun

private theorem sideBit_append_exact (xs ys : List Bool) :
    ∀ i : Nat, sideBit (xs ++ ys) i =
      if i < xs.length then sideBit xs i else sideBit ys (i-xs.length) := by
  intro i
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [sideBit]
      | succ i =>
          simp [sideBit, ih]

private theorem lbinDecHRunTape_preserves_left
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≤ h-(3*n:Int)-3) :
    lbinDecHRunTape n T h x = T x := by
  let h' : Int := h-(3*n:Int)
  let U : Int → Bool := sweptLeft (3*n) T h
  let V : Int → Bool := afterLIncBridge U h'
  have hU : U x = T x := by
    apply sweptLeft_preserves_left
    dsimp [h']
    omega
  have hx0 : x ≠ h'-1 := by omega
  have hx1 : x ≠ h' := by omega
  have hx2 : x ≠ h'+1 := by omega
  have hV : V x = U x := by
    simp [V, afterLIncBridge, hx0, hx1, hx2]
  have hR : sweptRightB n V (h'+2) x = V x := by
    apply sweptRightB_preserves_left
    omega
  simpa [lbinDecHRunTape, h', U, V] using hR.trans (hV.trans hU)

private theorem lbinDecHRunTape_d0_region
    (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) :
    ∀ i : Nat, i < 3*n →
      lbinDecHRunTape n T h (h-(i:Int)) = decide (i%3=2) := by
  intro i hi
  let h' : Int := h-(3*n:Int)
  let U : Int → Bool := sweptLeft (3*n) T h
  let V : Int → Bool := afterLIncBridge U h'
  have hright0 : rightOnes U (h'+2) n := by
    have hs := sweptLeft_rightOnes n T h hon
    simpa [U, h'] using hs
  have hrightV : rightOnes V (h'+2) n := by
    intro j hj
    obtain ⟨hA,hB,hC⟩ := hright0 j hj
    have hnA0 : h'+2+3*(j:Int) ≠ h'-1 := by omega
    have hnA1 : h'+2+3*(j:Int) ≠ h' := by omega
    have hnA2 : h'+2+3*(j:Int) ≠ h'+1 := by omega
    have hnB0 : h'+2+3*(j:Int)+1 ≠ h'-1 := by omega
    have hnB1 : h'+2+3*(j:Int)+1 ≠ h' := by omega
    have hnB2 : h'+2+3*(j:Int)+1 ≠ h'+1 := by omega
    have hnC0 : h'+2+3*(j:Int)+2 ≠ h'-1 := by omega
    have hnC1 : h'+2+3*(j:Int)+2 ≠ h' := by omega
    have hnC2 : h'+2+3*(j:Int)+2 ≠ h'+1 := by omega
    exact ⟨by simpa [V,afterLIncBridge,hnA0,hnA1,hnA2] using hA,
      by simpa [V,afterLIncBridge,hnB0,hnB1,hnB2] using hB,
      by simpa [V,afterLIncBridge,hnC0,hnC1,hnC2] using hC⟩
  have hcases : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
  let q : Nat := i/3
  let j : Nat := n-1-q
  have hdiv : i=3*q+i%3 := by dsimp [q]; omega
  have hq : q<n := by omega
  have hj : j<n := by dsimp [j]; omega
  rcases hcases with hmod0 | hmod1 | hmod2
  · have hcoord : h-(i:Int)=h'+2+3*(j:Int)+1 := by
      dsimp [h',j,q]
      omega
    have hb := sweptRightB_block n V (h'+2) hrightV j hj
    have hval : lbinDecHRunTape n T h (h-(i:Int)) = false := by
      rw [hcoord]
      simpa [lbinDecHRunTape,h',U,V] using hb.2.1
    simpa [hmod0] using hval
  · have hcoord : h-(i:Int)=h'+2+3*(j:Int) := by
      dsimp [h',j,q]
      omega
    have hb := sweptRightB_block n V (h'+2) hrightV j hj
    have hval : lbinDecHRunTape n T h (h-(i:Int)) = false := by
      rw [hcoord]
      simpa [lbinDecHRunTape,h',U,V] using hb.1
    simpa [hmod1] using hval
  · have hjcases : j=0 ∨ 0<j := by omega
    rcases hjcases with hj0 | hjpos
    · have hcoord : h-(i:Int)=h'+1 := by
        dsimp [h',j,q]
        omega
      have hp := sweptRightB_preserves_left n V (h'+2) (h'+1) (by omega)
      have hv : V (h'+1)=true := by simp [V,afterLIncBridge]
      have hval : lbinDecHRunTape n T h (h-(i:Int)) = true := by
        rw [hcoord]
        simpa [lbinDecHRunTape,h',U,V] using hp.trans hv
      simpa [hmod2] using hval
    · have hjm1 : j-1<n := by omega
      have hcoord : h-(i:Int)=h'+2+3*((j-1:Nat):Int)+2 := by
        dsimp [h',j,q]
        omega
      have hb := sweptRightB_block n V (h'+2) hrightV (j-1) hjm1
      have hval : lbinDecHRunTape n T h (h-(i:Int)) = true := by
        rw [hcoord]
        simpa [lbinDecHRunTape,h',U,V] using hb.2.2
      simpa [hmod2] using hval

/-- If the H-run starts with d1^n ++ d0 ++ tail when read head-facing,
then its output is exactly d0^n ++ d1 ++ tail. -/
theorem lbinDecHRunTape_leftFacing
    (n : Nat) (T : Int → Bool) (h : Int) (tail : List Bool)
    (hon : leftOnes T h (3*n))
    (h0 : T (h-(3*n:Int)) = false)
    (hm1 : T (h-(3*n:Int)-1) = false)
    (hthird : T (h-(3*n:Int)-2) = true)
    (hr : T (h+1) = false)
    (hleft : ∀ i : Nat, T (h-(i:Int)) =
      sideBit (d1pow n ++ (d0 ++ tail)) i) :
    ∀ i : Nat, lbinDecHRunTape n T h (h-(i:Int)) =
      sideBit (d0pow n ++ (d1 ++ tail)) i := by
  intro i
  by_cases hi0 : i < 3*n
  · have hb := lbinDecHRunTape_d0_region n T h hon i hi0
    have hside : sideBit (d0pow n ++ (d1 ++ tail)) i =
        decide (i%3=2) := by
      rw [sideBit_append_exact]
      rw [d0pow_length]
      simp [hi0, sideBit_d0pow_formula]
    rw [hb, hside]
  · by_cases hi1 : i < 3*n+3
    · have hmid : i=3*n ∨ i=3*n+1 ∨ i=3*n+2 := by omega
      rcases hmid with hmid0 | hmid1 | hmid2
      · subst i
        have hd1 := lbinDecHRunTape_d1 n T h hon h0 hm1 hthird hr
        rw [show h-((3*n:Nat):Int) = h-3*(n:Int) by omega, hd1.1]
        simp [sideBit_append_exact, d0pow_length, d1, sideBit, hi0] <;> omega
      · subst i
        have hd1 := lbinDecHRunTape_d1 n T h hon h0 hm1 hthird hr
        rw [show h-((3*n+1:Nat):Int) = h-3*(n:Int)-1 by omega, hd1.2.1]
        simp [sideBit_append_exact, d0pow_length, d1, sideBit, hi0] <;> omega
      · subst i
        have hd1 := lbinDecHRunTape_d1 n T h hon h0 hm1 hthird hr
        rw [show h-((3*n+2:Nat):Int) = h-3*(n:Int)-2 by omega, hd1.2.2]
        simp [sideBit_append_exact, d0pow_length, d1, sideBit, hi0] <;> omega
    · have hx : h-(i:Int) ≤ h-(3*n:Int)-3 := by omega
      rw [lbinDecHRunTape_preserves_left n T h (h-(i:Int)) hx]
      rw [hleft i]
      have hinput :
          sideBit (d1pow n ++ (d0 ++ tail)) i =
            sideBit tail (i-(3*n+3)) := by
        rw [sideBit_append_exact]
        rw [d1pow_length]
        have hnot1 : ¬ i < 3*n := by omega
        simp [hnot1]
        rw [sideBit_append_exact]
        have hnot2 : ¬ i-3*n < d0.length := by
          simp [d0]
          omega
        rw [if_neg hnot2]
        simp [d0]
        congr 1 <;> omega
      have houtput :
          sideBit (d0pow n ++ (d1 ++ tail)) i =
            sideBit tail (i-(3*n+3)) := by
        rw [sideBit_append_exact]
        rw [d0pow_length]
        have hnot1 : ¬ i < 3*n := by omega
        simp [hnot1]
        rw [sideBit_append_exact]
        have hnot2 : ¬ i-3*n < d1.length := by
          simp [d1]
          omega
        rw [if_neg hnot2]
        simp [d1]
        congr 1 <;> omega
      exact hinput.trans houtput.symm


/-- The B-sweep's rightmost cell is one; for n=0 this is the bridge's
rightmost write, and for n>0 it is the final sweptRightB block. -/
theorem lbinDecHRunTape_rightPlus1
    (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) :
    lbinDecHRunTape n T h (h+1) = true := by
  let h' : Int := h-(3*n:Int)
  let U : Int → Bool := sweptLeft (3*n) T h
  let V : Int → Bool := afterLIncBridge U h'
  have hright0 : rightOnes U (h'+2) n := by
    have hs := sweptLeft_rightOnes n T h hon
    simpa [U,h'] using hs
  have hrightV : rightOnes V (h'+2) n := by
    intro j hj
    obtain ⟨hA,hB,hC⟩ := hright0 j hj
    have hnA0 : h'+2+3*(j:Int) ≠ h'-1 := by omega
    have hnA1 : h'+2+3*(j:Int) ≠ h' := by omega
    have hnA2 : h'+2+3*(j:Int) ≠ h'+1 := by omega
    have hnB0 : h'+2+3*(j:Int)+1 ≠ h'-1 := by omega
    have hnB1 : h'+2+3*(j:Int)+1 ≠ h' := by omega
    have hnB2 : h'+2+3*(j:Int)+1 ≠ h'+1 := by omega
    have hnC0 : h'+2+3*(j:Int)+2 ≠ h'-1 := by omega
    have hnC1 : h'+2+3*(j:Int)+2 ≠ h' := by omega
    have hnC2 : h'+2+3*(j:Int)+2 ≠ h'+1 := by omega
    exact ⟨by simpa [V,afterLIncBridge,hnA0,hnA1,hnA2] using hA,
      by simpa [V,afterLIncBridge,hnB0,hnB1,hnB2] using hB,
      by simpa [V,afterLIncBridge,hnC0,hnC1,hnC2] using hC⟩
  by_cases hn0 : n=0
  · subst n
    have hp := sweptRightB_preserves_left 0 V (h'+2) (h'+1) (by omega)
    have hv : V (h'+1)=true := by simp [V,afterLIncBridge]
    have hcoord : h+1=h'+1 := by dsimp [h']; omega
    rw [hcoord]
    simpa [lbinDecHRunTape,h',U,V] using hp.trans hv
  · have hj : n-1<n := by omega
    have hb := sweptRightB_block n V (h'+2) hrightV (n-1) hj
    have hcoord :
        h+1=h'+2+3*((n-1:Nat):Int)+2 := by
      dsimp [h']
      omega
    rw [hcoord]
    simpa [lbinDecHRunTape,h',U,V] using hb.2.2


/-- Convenient source-facing API: the complete input word itself supplies
all three left-boundary facts needed by the counted H-run theorem. -/
theorem lbinDecHRunTape_leftFacing_of_input
    (n : Nat) (T : Int → Bool) (h : Int) (tail : List Bool)
    (hr : T (h+1) = false)
    (hleft : ∀ i : Nat, T (h-(i:Int)) =
      sideBit (d1pow n ++ (d0 ++ tail)) i) :
    ∀ i : Nat, lbinDecHRunTape n T h (h-(i:Int)) =
      sideBit (d0pow n ++ (d1 ++ tail)) i := by
  have hon : leftOnes T h (3*n) := by
    intro i hi
    rw [hleft i]
    rw [sideBit_append_exact]
    rw [d1pow_length]
    simp [hi,sideBit_d1pow_true]
  have h0 : T (h-(3*n:Int)) = false := by
    have hx := hleft (3*n)
    simpa [sideBit_append_exact,d1pow_length,d0,sideBit] using hx
  have hm1 : T (h-(3*n:Int)-1) = false := by
    have hx := hleft (3*n+1)
    have hcoord : h-(3*n:Int)-1 = h-((3*n+1):Int) := by omega
    rw [hcoord]
    simpa [sideBit_append_exact,d1pow_length,d0,sideBit,show ¬ 3*n+1<3*n by omega] using hx
  have hthird : T (h-(3*n:Int)-2) = true := by
    have hx := hleft (3*n+2)
    have hcoord : h-(3*n:Int)-2 = h-((3*n+2):Int) := by omega
    rw [hcoord]
    simpa [sideBit_append_exact,d1pow_length,d0,sideBit,show ¬ 3*n+2<3*n by omega] using hx
  exact lbinDecHRunTape_leftFacing n T h tail hon h0 hm1 hthird hr hleft

#print axioms lbinDecHRunTape_leftFacing
#print axioms lbinDecHRunTape_leftFacing_of_input
#print axioms lbinDecHRunTape_rightPlus1

end BB6Coverage.Agent24ChampionTime
