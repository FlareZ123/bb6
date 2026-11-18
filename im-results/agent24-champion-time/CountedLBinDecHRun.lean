import CountedSweep
import Lean.Elab.Tactic.Omega

/-!
# Universal LBinDec H-run for original TM63

A D-state left sweep over 3*n ones shifts that block one cell right.
A four-step D/C/E/A bridge turns the three-cell zero boundary into ones,
and a B/F/D right sweep consumes the shifted triples. The result is the
exact arbitrary-context 12*n+4 original-table run required by the Coq
LBinDec carry factorization.

This is a reusable physical source lemma, not by itself a complete
m=2,n=8*k reset-prefix proof or a BB(6) result.
-/

namespace BB6Coverage.Agent24LBinDecHRun

open BB6Coverage
open BB6Coverage.Agent48Champion

set_option maxHeartbeats 1000000

/-- The B/F/D rightward triple writes 0,0,1 and returns to B. -/
def afterRight3B (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h || x = h+1 then false else T x

private theorem lookupB1 :
    tm2 ((1 : Fin 6), true) = some ⟨false,true,5⟩ := by rfl
private theorem lookupF1 :
    tm2 ((5 : Fin 6), true) = some ⟨false,true,3⟩ := by rfl
private theorem lookupD1 :
    tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl

theorem counted_three_right_B (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = true) (h2 : T (h+2) = true) :
    run tm2 3 ⟨1,h,T⟩ = some ⟨1,h+3,afterRight3B T h⟩ := by
  have hh : h+1+1=h+2 := by omega
  have e01 : h+1 ≠ h := by omega
  have e02 : h+2 ≠ h := by omega
  have e12 : h+2 ≠ h+1 := by omega
  simp [run,rawStep,readSlot,applyMove,h0,h1,h2,hh,
    lookupB1,lookupF1,lookupD1,e01,e02,e12]
  constructor
  · omega
  · funext x
    by_cases hx0 : x=h <;> by_cases hx1 : x=h+1 <;>
      by_cases hx2 : x=h+2 <;>
      simp [afterRight3B,hx0,hx1,hx2,h2]

/-- Repeated B/F/D triples, with the exact whole-tape transformation. -/
def sweptRightB : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0,T,_ => T
  | n+1,T,h => sweptRightB n (afterRight3B T h) (h+3)

/-- The B/F/D sweep never changes cells strictly to the left of its start. -/
theorem sweptRightB_preserves_left (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : x < h) :
    sweptRightB n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      have hrec := ih (afterRight3B T h) (h+3) x (by omega)
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      have hafter : afterRight3B T h x = T x := by
        simp [afterRight3B,hne0,hne1]
      simpa [sweptRightB,hafter] using hrec

/-- The B/F/D sweep never changes cells at or beyond its final head. -/
theorem sweptRightB_preserves_right (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h+3*(n:Int) ≤ x) :
    sweptRightB n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      have hrec := ih (afterRight3B T h) (h+3) x (by omega)
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      have hafter : afterRight3B T h x = T x := by
        simp [afterRight3B,hne0,hne1]
      simpa [sweptRightB,hafter] using hrec

private theorem rightOnes_tail_B (T : Int → Bool) (h : Int) (n : Nat)
    (hon : rightOnes T h (n+1)) :
    rightOnes (afterRight3B T h) (h+3) n := by
  intro i hi
  obtain ⟨h0,h1,h2⟩ := hon (i+1) (by omega)
  have hcoord0 : h+3+3*(i:Int) = h+3*((i+1:Int)) := by omega
  have hcoord1 : h+3+3*(i:Int)+1 = h+3*((i+1:Int))+1 := by omega
  have hcoord2 : h+3+3*(i:Int)+2 = h+3*((i+1:Int))+2 := by omega
  have hne00 : h+3+3*(i:Int) ≠ h := by omega
  have hne01 : h+3+3*(i:Int) ≠ h+1 := by omega
  have hne10 : h+3+3*(i:Int)+1 ≠ h := by omega
  have hne11 : h+3+3*(i:Int)+1 ≠ h+1 := by omega
  have hne20 : h+3+3*(i:Int)+2 ≠ h := by omega
  have hne21 : h+3+3*(i:Int)+2 ≠ h+1 := by omega
  constructor
  · simpa [afterRight3B,hne00,hne01,hcoord0] using h0
  · constructor
    · simpa [afterRight3B,hne10,hne11,hcoord1] using h1
    · simpa [afterRight3B,hne20,hne21,hcoord2] using h2

theorem counted_right_sweep_B (n : Nat) (T : Int → Bool) (h : Int)
    (hon : rightOnes T h n) :
    run tm2 (3*n) ⟨1,h,T⟩ =
      some ⟨1,h+3*(n:Int),sweptRightB n T h⟩ := by
  induction n generalizing T h with
  | zero => simp [run,sweptRightB]
  | succ n ih =>
      obtain ⟨h0,h1,h2⟩ := hon 0 (by omega)
      have hstep := counted_three_right_B T h h0 h1 h2
      have hon' := rightOnes_tail_B T h n hon
      have htail := ih (afterRight3B T h) (h+3) hon'
      have hnum : 3*(n+1) = 3+3*n := by omega
      rw [hnum,run_append,hstep]
      simp only [Option.bind_some]
      rw [htail]
      have hhead : h+3+3*(n:Int) = h+3*((n+1):Int) := by omega
      simpa [sweptRightB,hhead]

/-- The fixed four-step D/C/E/A bridge fills the three zero cells. -/
def afterLIncBridge (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h-1 || x = h || x = h+1 then true else T x

private theorem lookupD0 :
    tm2 ((3 : Fin 6), false) = some ⟨false,false,2⟩ := by rfl
private theorem lookupC0 :
    tm2 ((2 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl
private theorem lookupE0 :
    tm2 ((4 : Fin 6), false) = some ⟨true,true,0⟩ := by rfl
private theorem lookupA0 :
    tm2 ((0 : Fin 6), false) = some ⟨true,true,1⟩ := by rfl

theorem counted_LIncBridge (T : Int → Bool) (h : Int)
    (hm1 : T (h-1) = false) (h0 : T h = false)
    (hp1 : T (h+1) = false) :
    run tm2 4 ⟨3,h,T⟩ = some ⟨1,h+2,afterLIncBridge T h⟩ := by
  have hleft : h+(-1)=h-1 := by omega
  have hback : h-1+1=h := by omega
  have hright : h+1+1=h+2 := by omega
  have e01 : h-1 ≠ h := by omega
  have e02 : h-1 ≠ h+1 := by omega
  have e12 : h ≠ h+1 := by omega
  simp [run,rawStep,readSlot,applyMove,hm1,h0,hp1,
    hleft,hback,hright,e01,e02,e12,
    lookupD0,lookupC0,lookupE0,lookupA0]
  funext x
  by_cases hx0 : x=h-1 <;> by_cases hx1 : x=h <;>
    by_cases hx2 : x=h+1 <;>
    simp [afterLIncBridge,hx0,hx1,hx2]

/-- A left sweep preserves every cell strictly before its leftmost
processed cell. -/
theorem sweptLeft_preserves_left (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : x < h-(n:Int)+1) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      have hrec := ih (holeThree T h) (h-1) (by omega)
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      have hafter : holeThree T h x = T x := by
        simp [holeThree,hne0,hne1]
      simpa [sweptLeft,hafter] using hrec

/-- A left sweep preserves every cell strictly to the right of its
initial right boundary. -/
theorem sweptLeft_preserves_right (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h+1 < x) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      have hrec := ih (holeThree T h) (h-1) (by omega)
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      have hafter : holeThree T h x = T x := by
        simp [holeThree,hne0,hne1]
      simpa [sweptLeft,hafter] using hrec

/-- The moving zero reaches the final processed cell of a left sweep. -/
theorem sweptLeft_boundary_right_zero (n : Nat) (T : Int → Bool)
    (h : Int) (hr : T (h+1) = false) :
    sweptLeft n T h (h-(n:Int)+1) = false := by
  induction n generalizing T h with
  | zero => simpa [sweptLeft] using hr
  | succ n ih =>
      have hne : h ≠ h+1 := by omega
      have hr' : holeThree T h ((h-1)+1) = false := by
        simp [holeThree, hne]
      have hrec := ih (holeThree T h) (h-1) hr'
      have hcoord : h-1-(n:Int)+1 = h-((n+1:Int))+1 := by omega
      simpa [sweptLeft,hcoord] using hrec

/-- After sweeping k left-facing ones, the block has shifted right by
one cell: its k output cells occupy h-k+2 through h+1. -/
theorem sweptLeft_shifted_block (k : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h k) :
    ∀ i : Nat, i<k →
      sweptLeft k T h (h-(k:Int)+2+(i:Int)) = true := by
  induction k generalizing T h with
  | zero => intro i hi; omega
  | succ k ih =>
      intro i hi
      by_cases hlast : i=k
      · subst i
        have hcoord : h-((↑(k+1)))+2+(k:Int) = h+1 := by omega
        rw [hcoord]
        have hpres := sweptLeft_preserves_right k
          (holeThree T h) (h-1) (h+1) (by omega)
        have hfirst : holeThree T h (h+1) = true := by
          simp [holeThree]
        calc
          sweptLeft (k+1) T h (h+1) =
              sweptLeft k (holeThree T h) (h-1) (h+1) := rfl
          _ = holeThree T h (h+1) := hpres
          _ = true := hfirst
      · have hi' : i<k := by omega
        have hon' : leftOnes (holeThree T h) (h-1) k :=
          leftOnes_tail T h k hon
        have hrec := ih (holeThree T h) (h-1) hon' i hi'
        have hcoord :
            h-((k+1:Int))+2+(i:Int) =
              (h-1)-(k:Int)+2+(i:Int) := by omega
        simpa [sweptLeft,hcoord] using hrec

/-- The shifted block is precisely n right-facing triples of ones. -/
theorem sweptLeft_rightOnes (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) :
    rightOnes (sweptLeft (3*n) T h) (h-(3*n:Int)+2) n := by
  intro i hi
  have h0 := sweptLeft_shifted_block (3*n) T h hon (3*i) (by omega)
  have h1 := sweptLeft_shifted_block (3*n) T h hon (3*i+1) (by omega)
  have h2 := sweptLeft_shifted_block (3*n) T h hon (3*i+2) (by omega)
  have hc0 : h-↑(3*n)+2+↑(3*i) =
      (h-(3*n:Int)+2)+3*(i:Int) := by omega
  have hc1 : h-↑(3*n)+2+↑(3*i+1) =
      (h-(3*n:Int)+2)+3*(i:Int)+1 := by omega
  have hc2 : h-↑(3*n)+2+↑(3*i+2) =
      (h-(3*n:Int)+2)+3*(i:Int)+2 := by omega
  rw [hc0] at h0
  rw [hc1] at h1
  rw [hc2] at h2
  exact ⟨h0,h1,h2⟩

/-- The three bridge cells are zero after the left sweep. -/
theorem sweptLeft_bridge_zeros (k : Nat) (T : Int → Bool) (h : Int)
    (h0 : T (h-(k:Int)) = false)
    (hm1 : T (h-(k:Int)-1) = false)
    (hr : T (h+1) = false) :
    sweptLeft k T h (h-(k:Int)) = false ∧
    sweptLeft k T h (h-(k:Int)-1) = false ∧
    sweptLeft k T h (h-(k:Int)+1) = false := by
  have hpres0 := sweptLeft_preserves_left k T h
    (h-(k:Int)) (by omega)
  have hpres1 := sweptLeft_preserves_left k T h
    (h-(k:Int)-1) (by omega)
  have hlast := sweptLeft_boundary_right_zero k T h hr
  constructor
  · rw [hpres0]
    exact h0
  · constructor
    · rw [hpres1]
      exact hm1
    · exact hlast

/-- The B/F/D sweep's exact triple output: each input 111 becomes 001
in increasing tape coordinates, with the whole exterior preserved. -/
theorem sweptRightB_block (n : Nat) (T : Int → Bool) (h : Int)
    (hon : rightOnes T h n) :
    ∀ i : Nat, i<n →
      sweptRightB n T h (h+3*(i:Int)) = false ∧
      sweptRightB n T h (h+3*(i:Int)+1) = false ∧
      sweptRightB n T h (h+3*(i:Int)+2) = true := by
  induction n generalizing T h with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      by_cases hi0 : i=0
      · subst i
        obtain ⟨h0,h1,h2⟩ := hon 0 (by omega)
        have hp0 := sweptRightB_preserves_left n
          (afterRight3B T h) (h+3) h (by omega)
        have hp1 := sweptRightB_preserves_left n
          (afterRight3B T h) (h+3) (h+1) (by omega)
        have hp2 := sweptRightB_preserves_left n
          (afterRight3B T h) (h+3) (h+2) (by omega)
        have ha0 : afterRight3B T h h = false := by
          simp [afterRight3B]
        have ha1 : afterRight3B T h (h+1) = false := by
          simp [afterRight3B]
        have hne20 : h+2 ≠ h := by omega
        have hne21 : h+2 ≠ h+1 := by omega
        have h2' : T (h+2) = true := by simpa using h2
        have ha2 : afterRight3B T h (h+2) = true := by
          simp [afterRight3B,hne20,hne21,h2']
        constructor
        · simpa [sweptRightB] using hp0.trans ha0
        · constructor
          · simpa [sweptRightB] using hp1.trans ha1
          · simpa [sweptRightB] using hp2.trans ha2
      · have hi' : i-1<n := by omega
        have hon' := rightOnes_tail_B T h n hon
        have hrec := ih (afterRight3B T h) (h+3) hon' (i-1) hi'
        have hc0 : h+3+3*((i:Int)-1) = h+3+3*((i-1):Int) := by omega
        have hc1 : h+3+3*((i:Int)-1)+1 = h+3+3*((i-1):Int)+1 := by omega
        have hc2 : h+3+3*((i:Int)-1)+2 = h+3+3*((i-1):Int)+2 := by omega
        simpa [sweptRightB,hc0,hc1,hc2] using hrec

/-- The exact final tape of the universal carry H-run. -/
def lbinDecHRunTape (n : Nat) (T : Int → Bool) (h : Int) : Int → Bool :=
  sweptRightB n
    (afterLIncBridge (sweptLeft (3*n) T h) (h-(3*n:Int)))
    (h-(3*n:Int)+2)

/-- The original TM63 executes the complete D-to-B LBinDec H-run in exactly
12*n+4 successful primitive transitions, for every n and every tape
context satisfying the left-one block, two zero boundary cells, and the
right zero boundary. -/
theorem counted_LBinDec_HRun (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n))
    (h0 : T (h-(3*n:Int)) = false)
    (hm1 : T (h-(3*n:Int)-1) = false)
    (hr : T (h+1) = false) :
    run tm2 (12*n+4) ⟨3,h,T⟩ =
      some ⟨1,h+2,lbinDecHRunTape n T h⟩ := by
  let k : Nat := 3*n
  let h' : Int := h-(k:Int)
  let U : Int → Bool := sweptLeft k T h
  let V : Int → Bool := afterLIncBridge U h'
  have hleft0 := sweptLeft_bridge_zeros k T h h0 hm1 hr
  have hz0 : U h' = false := by simpa [U,h'] using hleft0.1
  have hz1 : U (h'-1) = false := by simpa [U,h'] using hleft0.2.1
  have hz2 : U (h'+1) = false := by simpa [U,h'] using hleft0.2.2
  have hleftRun :
      run tm2 (9*n) ⟨3,h,T⟩ = some ⟨3,h',U⟩ := by
    have hs := counted_left_sweep k T h hon hr
    have hcost : 3*k = 9*n := by dsimp [k]; omega
    rw [hcost] at hs
    simpa [h',U] using hs
  have hbridge :
      run tm2 4 ⟨3,h',U⟩ = some ⟨1,h'+2,V⟩ :=
    counted_LIncBridge U h' hz1 hz0 hz2
  have hright0 : rightOnes U (h'+2) n := by
    have hs := sweptLeft_rightOnes n T h hon
    simpa [U,h',k] using hs
  have hrightV : rightOnes V (h'+2) n := by
    intro i hi
    obtain ⟨hA,hB,hC⟩ := hright0 i hi
    have hnA0 : h'+2+3*(i:Int) ≠ h'-1 := by omega
    have hnA1 : h'+2+3*(i:Int) ≠ h' := by omega
    have hnA2 : h'+2+3*(i:Int) ≠ h'+1 := by omega
    have hnB0 : h'+2+3*(i:Int)+1 ≠ h'-1 := by omega
    have hnB1 : h'+2+3*(i:Int)+1 ≠ h' := by omega
    have hnB2 : h'+2+3*(i:Int)+1 ≠ h'+1 := by omega
    have hnC0 : h'+2+3*(i:Int)+2 ≠ h'-1 := by omega
    have hnC1 : h'+2+3*(i:Int)+2 ≠ h' := by omega
    have hnC2 : h'+2+3*(i:Int)+2 ≠ h'+1 := by omega
    constructor
    · simpa [V,afterLIncBridge,hnA0,hnA1,hnA2] using hA
    · constructor
      · simpa [V,afterLIncBridge,hnB0,hnB1,hnB2] using hB
      · simpa [V,afterLIncBridge,hnC0,hnC1,hnC2] using hC
  have hrightRun := counted_right_sweep_B n V (h'+2) hrightV
  have hhead : h'+2+3*(n:Int) = h+2 := by
    dsimp [h',k]
    omega
  have hsplit : 12*n+4 = 9*n+(4+3*n) := by omega
  rw [hsplit,run_append,hleftRun]
  simp only [Option.bind_some]
  rw [run_append,hbridge]
  simp only [Option.bind_some]
  rw [hrightRun]
  simpa [lbinDecHRunTape,V,U,h',k,hhead]

/-- The H-run leaves the complete right exterior, beginning at its final
head, unchanged from the input tape. -/
theorem lbinDecHRunTape_preserves_right (n : Nat) (T : Int → Bool)
    (h : Int) (x : Int) (hx : h+2 ≤ x) :
    lbinDecHRunTape n T h x = T x := by
  let k : Nat := 3*n
  let h' : Int := h-(k:Int)
  let U : Int → Bool := sweptLeft k T h
  let V : Int → Bool := afterLIncBridge U h'
  have hleft : U x = T x := by
    apply sweptLeft_preserves_right
    omega
  have hbridge : V x = U x := by
    have hne0 : x ≠ h'-1 := by omega
    have hne1 : x ≠ h' := by omega
    have hne2 : x ≠ h'+1 := by omega
    simp [V,afterLIncBridge,hne0,hne1,hne2]
  have hright : sweptRightB n V (h'+2) x = V x := by
    apply sweptRightB_preserves_right
    dsimp [h',k]
    omega
  simpa [lbinDecHRunTape,k,h',U,V] using hright.trans (hbridge.trans hleft)

/-- The H-run output's final left boundary is d1: two bridge writes plus
the original final one of the d0 boundary block. -/
theorem lbinDecHRunTape_d1 (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n))
    (h0 : T (h-(3*n:Int)) = false)
    (hm1 : T (h-(3*n:Int)-1) = false)
    (hthird : T (h-(3*n:Int)-2) = true)
    (hr : T (h+1) = false) :
    lbinDecHRunTape n T h (h-(3*n:Int)) = true ∧
    lbinDecHRunTape n T h (h-(3*n:Int)-1) = true ∧
    lbinDecHRunTape n T h (h-(3*n:Int)-2) = true := by
  let k : Nat := 3*n
  let h' : Int := h-(k:Int)
  let U : Int → Bool := sweptLeft k T h
  let V : Int → Bool := afterLIncBridge U h'
  have hthirdU : U (h'-2) = true := by
    have hp := sweptLeft_preserves_left k T h (h'-2) (by omega)
    change sweptLeft k T h (h'-2) = true
    rw [hp]
    simpa [h',k] using hthird
  have hthirdV : V (h'-2) = true := by
    have hn0 : h'-2 ≠ h'-1 := by omega
    have hn1 : h'-2 ≠ h' := by omega
    have hn2 : h'-2 ≠ h'+1 := by omega
    simpa [V,afterLIncBridge,hn0,hn1,hn2] using hthirdU
  have hp0 : sweptRightB n V (h'+2) h' = V h' :=
    sweptRightB_preserves_left n V (h'+2) h' (by omega)
  have hp1 : sweptRightB n V (h'+2) (h'-1) = V (h'-1) :=
    sweptRightB_preserves_left n V (h'+2) (h'-1) (by omega)
  have hp2 : sweptRightB n V (h'+2) (h'-2) = V (h'-2) :=
    sweptRightB_preserves_left n V (h'+2) (h'-2) (by omega)
  have hv0 : V h'=true := by simp [V,afterLIncBridge]
  have hv1 : V (h'-1)=true := by simp [V,afterLIncBridge]
  have hw0 : sweptRightB n V (h'+2) h'=true := by rw [hp0,hv0]
  have hw1 : sweptRightB n V (h'+2) (h'-1)=true := by rw [hp1,hv1]
  have hw2 : sweptRightB n V (h'+2) (h'-2)=true := by
    rw [hp2]
    exact hthirdV
  simpa [lbinDecHRunTape,h',k,U,V] using ⟨hw0,hw1,hw2⟩

#print axioms counted_three_right_B
#print axioms counted_right_sweep_B
#print axioms counted_LIncBridge
#print axioms sweptLeft_shifted_block
#print axioms sweptLeft_rightOnes
#print axioms sweptRightB_block
#print axioms counted_LBinDec_HRun
#print axioms lbinDecHRunTape_preserves_right
#print axioms lbinDecHRunTape_d1

end BB6Coverage.Agent24LBinDecHRun
