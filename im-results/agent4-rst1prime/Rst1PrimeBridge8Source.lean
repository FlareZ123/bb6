import Rst1PrimeFirstSweep
import CountedRst1Prime
import CountedSuffixOutput
import Lean.Elab.Tactic.Omega

/-!
# Source-level first bridge in the Rst1' itinerary

After the first 3a+1 counted left sweep, the four-cell window [-3,0]
is exactly the finite bridge8 input.  This is proved against the complete
infinite S1 tape: the sweep changes no cell at or left of its new head,
and the remaining marker/d0 source word supplies the bridge window.
The resulting bridge is then lifted by Agent 8's exact bridgeAt theorem.
-/

namespace BB6Coverage.Agent4Rst1Prime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent8Rst1Prime

/-- The counted left sweep does not alter any cell at or left of its
new head. -/
theorem sweptLeft_eq_of_le
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≤ h-(n:Int)) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [sweptLeft]
  | succ n ih =>
      have hx' : x ≤ (h-1)-(n:Int) := by omega
      rw [sweptLeft]
      rw [ih (holeThree T h) (h-1) hx']
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      have hne2 : x ≠ h+2 := by omega
      simp [holeThree,hne0,hne1,hne2]

/-- Source cells immediately beyond the swept d1^a ++ markerWord 1
prefix.  The index k=0 is markerWord 1's second bit. -/
theorem s1Config_left_after_d1pow
    (L a b : Nat) (h : Int) (k : Nat) :
    (s1Config L 0 1 a 0 b h).tape
      (h-((3*a+1+k:Int))) =
      sideBit (markerWord 1 ++ d0 ++ binDec L 0 ++ lh) (k+1) := by
  have hcast : ((3*a+1+k : Nat) : Int) =
      3*(a:Int)+1+(k:Int) := by
    omega
  rw [← hcast]
  rw [s1Config_left_cell L 0 1 a 0 b h (3*a+1+k)]
  simp only [s1LeftFacing,binDec_zero]
  rw [sideBit_append]
  rw [d1pow_length]
  have hlt : ¬ 3*a+1+k < 3*a := by omega
  simp only [if_neg hlt]
  have hindex : 3*a+1+k-3*a = k+1 := by omega
  simpa [hindex]

/-- The post-sweep local tape is exactly bridge8Start on its entire
queried window [-3,0]. -/
theorem rst1Prime_bridge8_window_after_firstSweep
    (L a b : Nat) (h : Int) :
    ∀ x, inside8 x = true →
      (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
        (h-((3*a+1:Int))+x) =
        decide (x ∈ bridge8Start.marked) := by
  intro x hx
  have hxw : -3 ≤ x ∧ x ≤ 0 := by
    simpa [inside8,inWindow] using hx
  have hle : h-((3*a+1:Int))+x ≤ h-((3*a+1:Int)) := by omega
  have hunchanged :=
    sweptLeft_eq_of_le (3*a+1) (s1Config L 0 1 a 0 b h).tape h
      (h-((3*a+1:Int))+x) hle
  rw [hunchanged]
  have hcases : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 := by omega
  rcases hcases with h3 | h2 | h1 | h0
  · subst x
    have hcoord :
        h-((3*a+1:Int))+(-3:Int) = h-(3*(a:Int)+1+((3:Nat):Int)) := by omega
    rw [hcoord,s1Config_left_after_d1pow L a b h 3]
    simp [markerWord,d0,sideBit,bridge8Start]
  · subst x
    have hcoord :
        h-((3*a+1:Int))+(-2:Int) = h-(3*(a:Int)+1+((2:Nat):Int)) := by omega
    rw [hcoord,s1Config_left_after_d1pow L a b h 2]
    simp [markerWord,d0,sideBit,bridge8Start]
  · subst x
    have hcoord :
        h-((3*a+1:Int))+(-1:Int) = h-(3*(a:Int)+1+((1:Nat):Int)) := by omega
    rw [hcoord,s1Config_left_after_d1pow L a b h 1]
    simp [markerWord,d0,sideBit,bridge8Start]
  · subst x
    have hcoord :
        h-((3*a+1:Int))+(0:Int) = h-(3*(a:Int)+1+((0:Nat):Int)) := by omega
    rw [hcoord,s1Config_left_after_d1pow L a b h 0]
    simp [markerWord,d0,sideBit,bridge8Start]

/-- The first Rst1' bridge is now a genuine original-machine run from the
S1 source, not merely a finite-frame computation. -/
theorem rst1Prime_bridge8_after_firstSweep
    (L a b : Nat) (h : Int) :
    run tm2 (9*a+3+8) (s1Config L 0 1 a 0 b h) =
      some (frameAt
        (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
        (h-((3*a+1:Int))) inside8 bridge8End) := by
  rw [run_append,rst1Prime_firstSweep_run]
  simp only [Option.bind_some]
  exact bridge8_at
    (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
    (h-((3*a+1:Int)))
    (rst1Prime_bridge8_window_after_firstSweep L a b h)

#print axioms sweptLeft_eq_of_le
#print axioms s1Config_left_after_d1pow
#print axioms rst1Prime_bridge8_window_after_firstSweep
#print axioms rst1Prime_bridge8_after_firstSweep

end BB6Coverage.Agent4Rst1Prime
