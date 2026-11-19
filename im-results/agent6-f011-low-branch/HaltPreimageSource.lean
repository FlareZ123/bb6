/-
Source-import bridge for the F011 scalar rank.

Compile inside google-deepmind/cryptids at the pinned source revision
c86f15861709b76042998c5211c7b2f83991621b, with this directory on LEAN_PATH.
The upstream HighLevelState and highLevelNext are public. The map bridge below
is intended to be definitional (rfl): it identifies the literal copied
AuditState transition with the upstream transition after mapping constructors.

This file is a draft until the copied rank theorem in HaltPreimageRank.lean
passes local preflight and this file is compiled against the pinned upstream
dependency closure. No axiom or sorry is used here.
-/
import BusyBeaver.BB6.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD
import HaltPreimageRank

namespace F011

open BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD

def toAuditState : HighLevelState → AuditState
  | .S p k c => AuditState.S p k c

theorem highLevelNext_toAudit (p : Bool) (k c : Nat) :
    (highLevelNext (.S p k c)).map toAuditState =
      auditHighLevelNext (AuditState.S p k c) := by
  rfl

def SourceScalarRank : HighLevelState → Nat
  | .S p k c => 2 * Potential p k c + ResidueTieBreak k

/-- Every defined upstream high-level transition strictly raises the scalar rank. -/
theorem source_scalar_rank_strict
    (p p' : Bool) (k c k' c' : Nat)
    (h : highLevelNext (.S p k c) = some (.S p' k' c')) :
    SourceScalarRank (.S p k c) < SourceScalarRank (.S p' k' c') := by
  have hAudit : auditHighLevelNext (AuditState.S p k c) =
      some (AuditState.S p' k' c') := by
    have hh := congrArg (Option.map toAuditState) h
    rw [highLevelNext_toAudit] at hh
    simpa [toAuditState] using hh
  have hPair := rank_strict p p' k c k' c' hAudit
  unfold LexLt Rank at hPair
  unfold SourceScalarRank
  rcases hPair with hW | ⟨hW, hTie⟩ <;> omega


/-- Iterate the original-source high-level transition exactly n times. -/
def sourceIterate : Nat → HighLevelState → Option HighLevelState
  | 0, s => some s
  | n + 1, s => (highLevelNext s).bind (sourceIterate n)

/-- Every defined n-step source orbit increases the scalar rank by at least n. -/
theorem source_iterate_rank_growth :
    ∀ n s t, sourceIterate n s = some t →
      SourceScalarRank s + n ≤ SourceScalarRank t := by
  intro n
  induction n with
  | zero =>
      intro s t h
      simp [sourceIterate] at h
      cases h
      simp
  | succ n ih =>
      intro s t h
      cases s with
      | S p k c =>
          simp only [sourceIterate] at h
          cases hstep : highLevelNext (.S p k c) with
          | none =>
              simp [hstep] at h
          | some s1 =>
              simp [hstep] at h
              have hfirst : SourceScalarRank (.S p k c) + 1 ≤ SourceScalarRank s1 := by
                cases s1 with
                | S p' k' c' =>
                    exact Nat.succ_le_iff.mpr
                      (source_scalar_rank_strict p p' k c k' c' hstep)
              have hrest := ih s1 t h
              omega

/-- No positive-length orbit of the original-source high-level map is cyclic. -/
theorem source_no_positive_cycle (n : Nat) (s : HighLevelState) (hn : 0 < n) :
    sourceIterate n s ≠ some s := by
  intro h
  have hg := source_iterate_rank_growth n s s h
  omega

end F011

#print axioms F011.source_scalar_rank_strict
#print axioms F011.source_iterate_rank_growth
#print axioms F011.source_no_positive_cycle
