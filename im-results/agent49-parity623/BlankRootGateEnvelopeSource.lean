import Agent1ComplementBufferSource
import Agent8RootCorridorSource
import Agent49AffinePredecessorBoundsSource

/-!
Unconditional root-terminal predecessor reduction for original-source #623.

A blank-root state with a halting daughter must lie in the old affine cone.
Unlike the earlier GatePredecessor theorem, this needs no hypothesis that
the root state already lies in the newer exponential cone:

* the zero-first-counter case is excluded by Agent 8's rooted two-step result;
* every positive even state outside the old cone has a successful daughter,
  by Agent 1's complementary affine buffer plus Agent 49's new-to-old buffer.

The four exact affine predecessor envelopes then apply to every hypothetical
blank-root terminal transition. This is still a necessary condition, not a
decision of the genuine root.
-/

namespace BB6.Agent49BlankRootGateEnvelopeSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryBufferSource
open BB6.Agent49PredecessorBoundsSource
open BB6.Agent1ComplementBufferSource
open BB6.Agent8RootCorridorSource

/-- Every genuine blank-root terminal transition has its parent in the
old four-sector affine cone, without assuming membership in newAffineCone. -/
theorem blank_run_terminal_parent_oldAffine
    (n a d b e : Nat)
    (hseen : run n = some (.D a d))
    (hnext : highLevelNext (.D a d) = some (.D b e))
    (hhalt : highLevelNext (.D b e) = none) :
    oldAffineCone a d := by
  by_cases ha0 : a = 0
  · have hsafe :=
      blank_root_zero_a_no_immediate_daughter_halt n d b e hseen hnext
    exact False.elim (hsafe hhalt)
  · have heven := run_preserves_even n a d hseen
    have hpos : 0 < a := by omega
    by_contra hnot
    obtain ⟨c, f, hcont⟩ :=
      outside_old_predecessor_has_successor a d b e heven hpos hnot hnext
    rw [hhalt] at hcont
    cases hcont

/-- The four finite affine predecessor envelopes apply to every hypothetical
blank-root terminal transition, with no new-cone premise. -/
theorem blank_run_terminal_parent_finite_envelope
    (n a d b e : Nat)
    (hseen : run n = some (.D a d))
    (hnext : highLevelNext (.D a d) = some (.D b e))
    (hhalt : highLevelNext (.D b e) = none) :
    (a ≤ b + 2*d + 8 ∧ 3*d + 14 ≤ e) ∨
    (a ≤ b + 2*d + 4 ∧ 3*d + 8 ≤ e) ∨
    (d ≤ b + 2*a + 1 ∧ 3*a ≤ e) ∨
    (d ≤ b + 2*a + 2 ∧ 2*a + 5 ≤ e) := by
  have hold :=
    blank_run_terminal_parent_oldAffine n a d b e hseen hnext hhalt
  rcases hold with ⟨hd, hside⟩ | ⟨hd, hside⟩ |
      ⟨ha0, he, hd, hside⟩ | ⟨ha0, he, hd, hside⟩
  · exact Or.inl
      (farLeftOdd_predecessor_envelope a d b e hd (by omega) hnext)
  · exact Or.inr (Or.inl
      (farLeftEven_predecessor_envelope a d b e hd (by omega) hnext))
  · exact Or.inr (Or.inr (Or.inl
      (farRightOdd_predecessor_envelope a d b e ha0 he hd (by omega) hnext)))
  · exact Or.inr (Or.inr (Or.inr
      (farRightEven_predecessor_envelope a d b e ha0 he hd (by omega) hnext)))

#print axioms blank_run_terminal_parent_oldAffine
#print axioms blank_run_terminal_parent_finite_envelope

end BB6.Agent49BlankRootGateEnvelopeSource
