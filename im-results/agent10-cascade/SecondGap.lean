import ResetAncestry
import TerminalExit

namespace CascadeTwoLevelGap
open CascadeSource CascadeSweep CascadeAncestry

/-- A two-generation root obstruction for completed reset heights.

    If a non-odd-return reset `h` lies in the even-image dyadic band
    at level `m`, its only possible genuine parent is the uniquely
    determined `x`, satisfying `2h=8*2^m+x+m`.
    When `x` itself has the forbidden odd residue and lies in the open
    even-image gap at exactly this level, neither parent can occur on the
    genuine source trajectory from (2,0).  This excludes an infinite,
    recursively described family of reset heights with nontrivial
    *two-reset* ancestry. -/
theorem root_excludes_two_level_gap (m h x : Nat) (hm : 1 ≤ m)
    (hmod : h%3 ≠ 2)
    (hband : 6*2^m-1 ≤ h ∧ h ≤ 8*2^m-3)
    (hparent : 2*h = 8*2^m+x+m)
    (xmod : x%3 ≠ 2)
    (xlo : 4*2^m-3 < x)
    (xhi : x < 6*2^m-1) :
    ¬ ReachC (2,0) (h,0) := by
  intro hr
  obtain ⟨parent, k, hreach, hlo, hhi, heq⟩ :=
    reachable_even_reset_parent h hr hmod
  have hk : k=m :=
    even_band_unique h k m ⟨hlo,hhi⟩ hband
  subst k
  have hparent_eq : parent = x := by omega
  subst parent
  have hno : ∀ i, ¬(6*2^i-1 ≤ x ∧ x ≤ 8*2^i-3) := by
    intro i
    exact TerminalExit.no_even_band (m+1) i x (by omega)
      (by simpa [Nat.add_sub_cancel_left, Nat.pow_succ] using xlo)
      (by simpa [Nat.add_sub_cancel_left, Nat.pow_succ] using xhi)
  exact (root_excludes_nonimage x xmod hno) hreach

#print axioms root_excludes_two_level_gap
end CascadeTwoLevelGap
