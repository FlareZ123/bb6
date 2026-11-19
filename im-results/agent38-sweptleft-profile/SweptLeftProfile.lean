import CountedSweep
import Lean.Elab.Tactic.Omega

/-!
# Exact four-region tape profile of the counted left sweep

For the original TM63 state-3 left sweep, a contiguous run of n ones
and a blank immediately to its right determine the entire changed
interval, not merely the final head position:

* cells strictly left of the final moving-zero boundary are unchanged;
* the boundary cell is zero;
* the cells from the next cell through the original right neighbour
  are all one;
* cells strictly right of the original right neighbour are unchanged.

This is a reusable pointwise invariant for composing the sweep with
finite source bridges.  It is an intermediate theorem until compiled
against the pinned Lean toolchain and the exact import closure.
-/

namespace BB6Coverage.Agent38SweptLeftProfile

open BB6Coverage
open BB6Coverage.Agent48Champion

/-- Exact four-region profile of the original counted left sweep. -/
theorem sweptLeft_four_region_profile
    (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false) :
    (∀ x : Int, x < h-(n:Int)+1 →
      sweptLeft n T h x = T x) ∧
    sweptLeft n T h (h-(n:Int)+1) = false ∧
    (∀ x : Int, h-(n:Int)+2 ≤ x → x ≤ h+1 →
      sweptLeft n T h x = true) ∧
    (∀ x : Int, h+1 < x →
      sweptLeft n T h x = T x) := by
  induction n generalizing T h with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        rfl
      · simpa [sweptLeft] using hr
      · intro x hlo hhi
        omega
      · intro x hx
        rfl
  | succ n ih =>
      have hon' : leftOnes (holeThree T h) (h-1) n :=
        leftOnes_tail T h n hon
      have hhead : (h-1)+1 = h := by omega
      have hr' : holeThree T h ((h-1)+1) = false := by
        rw [hhead]
        simp [holeThree]
      have hp := ih (holeThree T h) (h-1) hon' hr'
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        have hx' : x < (h-1)-(n:Int)+1 := by omega
        have hrec := hp.1 x hx'
        have hne0 : x ≠ h := by omega
        have hne1 : x ≠ h+1 := by omega
        have hpres : holeThree T h x = T x := by
          simp [holeThree, hne0, hne1]
        simpa [sweptLeft] using hrec.trans hpres
      · have heq :
            h-((n+1 : Nat) : Int)+1 =
              (h-1)-(n:Int)+1 := by omega
        rw [heq]
        simpa [sweptLeft] using hp.2.1
      · intro x hlo hhi
        by_cases hle : x ≤ h
        · have hrec := hp.2.2.1 x (by omega) (by omega)
          simpa [sweptLeft] using hrec
        · have hxEq : x = h+1 := by omega
          subst x
          have hrec := hp.2.2.2 (h+1) (by omega)
          simpa [sweptLeft, holeThree] using hrec
      · intro x hx
        have hrec := hp.2.2.2 x (by omega)
        have hne0 : x ≠ h := by omega
        have hne1 : x ≠ h+1 := by omega
        have hpres : holeThree T h x = T x := by
          simp [holeThree, hne0, hne1]
        simpa [sweptLeft] using hrec.trans hpres

/-- The sweep preserves every cell strictly before its final boundary. -/
theorem sweptLeft_preserves_before
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false)
    (hx : x < h-(n:Int)+1) :
    sweptLeft n T h x = T x :=
  (sweptLeft_four_region_profile n T h hon hr).1 x hx

/-- The final moving-zero boundary is blank. -/
theorem sweptLeft_boundary_zero
    (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false) :
    sweptLeft n T h (h-(n:Int)+1) = false :=
  (sweptLeft_four_region_profile n T h hon hr).2.1

/-- The sweep fills the interval immediately to the right of its boundary. -/
theorem sweptLeft_fills_interval
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false)
    (hlo : h-(n:Int)+2 ≤ x) (hhi : x ≤ h+1) :
    sweptLeft n T h x = true :=
  (sweptLeft_four_region_profile n T h hon hr).2.2.1 x hlo hhi

/-- The sweep preserves every cell strictly right of the original neighbour. -/
theorem sweptLeft_preserves_after
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false)
    (hx : h+1 < x) :
    sweptLeft n T h x = T x :=
  (sweptLeft_four_region_profile n T h hon hr).2.2.2 x hx

#print axioms sweptLeft_four_region_profile
#print axioms sweptLeft_preserves_before
#print axioms sweptLeft_boundary_zero
#print axioms sweptLeft_fills_interval
#print axioms sweptLeft_preserves_after

end BB6Coverage.Agent38SweptLeftProfile
