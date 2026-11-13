import Rst1PrimeSecondSweep
import CountedRst1Prime
import CountedSuffixOutput
import Lean.Elab.Tactic.Omega

/-!
# Source-level bridge20 and right-sweep continuation for Rst1'

The second counted left sweep leaves a contiguous block of 3L+5 ones
immediately to the right of its new head.  The bridge20 window is
obtained from the remaining lh suffix on the left and the exact
sweptLeft pattern on the right.  After bridge20 moves the head four
cells right, the remaining L+1 triples are still inside that swept
one-block, so the counted right sweep applies.
-/

namespace BB6Coverage.Agent4Rst1Prime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent8Rst1Prime

/-- Cells strictly to the right of the first holeThree window are
unchanged by any number of subsequent left-sweep steps. -/
theorem sweptLeft_eq_of_gt
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : h+1 < x) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [sweptLeft]
  | succ n ih =>
      rw [sweptLeft]
      have hx' : (h-1)+1 < x := by omega
      rw [ih (holeThree T h) (h-1) x hx']
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      simp [holeThree,hne0,hne1]

/-- The cell immediately right of the new head is zero after a
positive-length counted left sweep. -/
theorem sweptLeft_head_plus1_eq_false
    (n : Nat) (T : Int → Bool) (h : Int)
    (hn : 0<n) :
    sweptLeft n T h (h-(n:Int)+1) = false := by
  cases n with
  | zero =>
      omega
  | succ n =>
      induction n generalizing T h with
      | zero =>
          simp [sweptLeft,holeThree]
      | succ n ih =>
          have hcoord :
              h-((n+2:Int))+1 = (h-1)-((n+1:Int))+1 := by omega
          rw [sweptLeft,hcoord]
          exact ih (holeThree T h) (h-1)

/-- The left-sweep output contains a contiguous block of n ones from
its new head+2 through the original head+1. -/
theorem sweptLeft_one_block
    (n : Nat) (T : Int → Bool) (h : Int)
    (j : Nat) (hj : j<n) :
    sweptLeft n T h (h-(n:Int)+2+(j:Int)) = true := by
  induction n generalizing T h j with
  | zero =>
      omega
  | succ n ih =>
      by_cases hjn : j<n
      · have hcoord :
          h-((n+1:Int))+2+(j:Int) =
            (h-1)-(n:Int)+2+(j:Int) := by omega
        rw [sweptLeft,hcoord]
        exact ih (holeThree T h) (h-1) j hjn
      · have heq : j=n := by omega
        subst j
        rw [sweptLeft]
        have hcoord :
            h-((n+1:Int))+2+(n:Int) = h+1 := by omega
        rw [hcoord]
        have htail :
            sweptLeft n (holeThree T h) (h-1) (h+1) =
              holeThree T h (h+1) := by
          apply sweptLeft_eq_of_gt
          omega
        rw [htail]
        simp [holeThree]

/-- Beyond the fixed marker/d0 prefix and the d1^L block, the source
left-facing word is exactly lh. -/
theorem rst1Prime_source_lh_cell
    (L r : Nat) :
    sideBit (markerWord 1 ++ d0 ++ binDec L 0 ++ lh)
      (3*L+6+r) = sideBit lh r := by
  have hmark : (markerWord 1).length = 3 := by decide
  have hd0 : d0.length = 3 := by decide
  have hbin : (binDec L 0).length = 3*L := by
    rw [binDec_zero,d1pow_length]
  rw [sideBit_append,hmark]
  have hnot1 : ¬ 3*L+6+r < 3 := by omega
  simp only [if_neg hnot1]
  have hindex1 : 3*L+6+r-3 = 3*L+3+r := by omega
  rw [hindex1,sideBit_append,hd0]
  have hnot2 : ¬ 3*L+3+r < 3 := by omega
  simp only [if_neg hnot2]
  have hindex2 : 3*L+3+r-3 = 3*L+r := by omega
  rw [hindex2,sideBit_append,hbin]
  have hnot3 : ¬ 3*L+r < 3*L := by omega
  simp only [if_neg hnot3]
  have hindex3 : 3*L+r-3*L = r := by omega
  rw [hindex3]

/-- Left cells in the bridge20 window come from lh after the first
two lh ones were consumed by the second sweep. -/
theorem rst1Prime_bridge20_left_cell
    (L a b : Nat) (h : Int) (k : Nat) (hk : k≤5) :
    (sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-2))
      ((h-((3*a+1:Int))-2)-((3*L+5:Int))-(k:Int)) =
      sideBit lh (2+k) := by
  let H0 : Int := h-((3*a+1:Int))
  let H1 : Int := H0-2
  let H2 : Int := H1-((3*L+5:Int))
  let T1 : Int → Bool :=
    sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h
  let T2 : Int → Bool := frameAt T1 H0 inside8 bridge8End
  change (sweptLeft (3*L+5) T2 H1) (H2-(k:Int)) =
    sideBit lh (2+k)
  have hunchanged2 :
      sweptLeft (3*L+5) T2 H1 (H2-(k:Int)) = T2 (H2-(k:Int)) := by
    apply sweptLeft_eq_of_le
    dsimp [H2]
    omega
  rw [hunchanged2]
  have hrel : (H2-(k:Int))-H0 = -((3*L+7+k:Int)) := by
    dsimp [H2,H1]
    omega
  have hout : inside8 ((H2-(k:Int))-H0) = false := by
    simp [inside8,inWindow,hrel]
    omega
  rw [frameAt_tape]
  simp only [hout]
  have hunchanged1 :
      sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h
        (H2-(k:Int)) =
      (s1Config L 0 1 a 0 b h).tape (H2-(k:Int)) := by
    apply sweptLeft_eq_of_le
    dsimp [H0,H1,H2]
    omega
  rw [hunchanged1]
  have hcoord :
      H2-(k:Int) = h-((3*a+1+(3*L+7+k):Int)) := by
    dsimp [H0,H1,H2]
    omega
  rw [hcoord,s1Config_left_after_d1pow]
  have hindex : 3*L+8+k = 3*L+6+(2+k) := by omega
  rw [hindex,rst1Prime_source_lh_cell]

/-- The complete bridge20 input window after the second counted sweep. -/
theorem rst1Prime_bridge20_window_after_secondSweep
    (L a b : Nat) (h : Int) :
    ∀ x, inside20 x = true →
      (sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
        (h-((3*a+1:Int))-2))
        ((h-((3*a+1:Int))-2)-((3*L+5:Int))+x) =
        decide (x ∈ bridge20Start.marked) := by
  intro x hx
  have hxw : -5 ≤ x ∧ x ≤ 3 := by
    simpa [inside20,inWindow] using hx
  have hcases :
      x = -5 ∨ x = -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  rcases hcases with h5 | h4 | h3 | h2 | h1 | h0 | hpos1 | hpos2 | hpos3
  · subst x
    have hcell := rst1Prime_bridge20_left_cell L a b h 5 (by omega)
    simpa [bridge20Start,lh,sideBit] using hcell
  · subst x
    have hcell := rst1Prime_bridge20_left_cell L a b h 4 (by omega)
    simpa [bridge20Start,lh,sideBit] using hcell
  · subst x
    have hcell := rst1Prime_bridge20_left_cell L a b h 3 (by omega)
    simpa [bridge20Start,lh,sideBit] using hcell
  · subst x
    have hcell := rst1Prime_bridge20_left_cell L a b h 2 (by omega)
    simpa [bridge20Start,lh,sideBit] using hcell
  · subst x
    have hcell := rst1Prime_bridge20_left_cell L a b h 1 (by omega)
    simpa [bridge20Start,lh,sideBit] using hcell
  · subst x
    have hcell := rst1Prime_bridge20_left_cell L a b h 0 (by omega)
    simpa [bridge20Start,lh,sideBit] using hcell
  · subst x
    have hfalse := sweptLeft_head_plus1_eq_false
      (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-2) (by omega)
    simpa [bridge20Start] using hfalse
  · subst x
    have htrue := sweptLeft_one_block
      (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-2) 0 (by omega)
    simpa [bridge20Start] using htrue
  · subst x
    have htrue := sweptLeft_one_block
      (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-2) 1 (by omega)
    simpa [bridge20Start] using htrue

/-- Full original-source configuration after bridge20. -/
def rst1PrimeAfterBridge20
    (L a b : Nat) (h : Int) : Config :=
  frameAt
    (sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-2))
    ((h-((3*a+1:Int))-2)-((3*L+5:Int)))
    inside20 bridge20End

/-- Compose the second sweep with the exact 20-step bridge. -/
theorem rst1Prime_bridge20_after_secondSweep
    (L a b : Nat) (h : Int) :
    run tm2 (9*a+3+8+3*(3*L+5)+20)
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterBridge20 L a b h) := by
  rw [run_add,rst1Prime_secondSweep_run]
  simp only [Option.bind_some]
  exact bridge20_at
    (sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-2))
    ((h-((3*a+1:Int))-2)-((3*L+5:Int)))
    (rst1Prime_bridge20_window_after_secondSweep L a b h)

/-- The bridge20 output leaves L+1 full triples of ones to its right,
so the third (rightward) counted sweep is available. -/
theorem rst1Prime_rightSweep_preconditions_after_bridge20
    (L a b : Nat) (h : Int) :
    rightOnes (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4) (L+1) := by
  let H1 : Int := h-((3*a+1:Int))-2
  let H2 : Int := H1-((3*L+5:Int))
  let T2 : Int := (rst1PrimeAfterBridge8 L a b h).tape
  let T3 : Int → Bool := sweptLeft (3*L+5) T2 H1
  change rightOnes (frameAt T3 H2 inside20 bridge20End).tape
    (H2+4) (L+1)
  intro i hi
  have hone (k : Nat) (hk : k≤2) :
      (frameAt T3 H2 inside20 bridge20End).tape
        (H2+4+3*(i:Int)+(k:Int)) = true := by
    have hrel :
        (H2+4+3*(i:Int)+(k:Int))-H2 =
          4+3*(i:Int)+(k:Int) := by omega
    have hout :
        inside20 ((H2+4+3*(i:Int)+(k:Int))-H2) = false := by
      simp [inside20,inWindow,hrel]
      omega
    rw [frameAt_tape]
    simp only [hout]
    have hcoord :
        H2+4+3*(i:Int)+(k:Int) =
          H1-((3*L+5:Int))+2+((2+3*i+k:Int)) := by
      dsimp [H2]
      omega
    rw [hcoord]
    have hj : 2+3*i+k < 3*L+5 := by omega
    exact sweptLeft_one_block (3*L+5) T2 H1 (2+3*i+k) hj
  have h0 := hone 0 (by omega)
  have h1 := hone 1 (by omega)
  have h2 := hone 2 (by omega)
  exact ⟨h0,by simpa using h1,by simpa using h2⟩

/-- Exact original-machine run through bridge20 and the following
L+1-block rightward sweep. -/
theorem rst1Prime_rightSweep_after_bridge20_run
    (L a b : Nat) (h : Int) :
    run tm2 (9*a+3+8+3*(3*L+5)+20+3*(L+1))
      (s1Config L 0 1 a 0 b h) =
      some ⟨3,
        (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)+
          3*((L+1):Int),
        sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape
          (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)⟩ := by
  have hprefix := rst1Prime_bridge20_after_secondSweep L a b h
  have hpre := rst1Prime_rightSweep_preconditions_after_bridge20 L a b h
  have hrun := counted_right_sweep (L+1)
    (rst1PrimeAfterBridge20 L a b h).tape
    (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4) hpre
  rw [run_add,hprefix]
  simp only [Option.bind_some]
  simpa [rst1PrimeAfterBridge20,frameAt_state,frameAt_head,bridge20End] using hrun

#print axioms sweptLeft_eq_of_gt
#print axioms sweptLeft_one_block
#print axioms rst1Prime_source_lh_cell
#print axioms rst1Prime_bridge20_left_cell
#print axioms rst1Prime_bridge20_window_after_secondSweep
#print axioms rst1Prime_bridge20_after_secondSweep
#print axioms rst1Prime_rightSweep_preconditions_after_bridge20
#print axioms rst1Prime_rightSweep_after_bridge20_run

end BB6Coverage.Agent4Rst1Prime
