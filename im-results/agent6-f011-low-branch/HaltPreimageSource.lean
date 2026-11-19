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

end F011
