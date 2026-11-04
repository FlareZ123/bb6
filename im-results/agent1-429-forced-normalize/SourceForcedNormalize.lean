import SourceRawHalt86
import BB429ForcedNormalize

namespace BB429SourceForcedNormalize
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Computable original-source all-time blank-root nonreachability test. -/
theorem source_forcedExcluded_sound (a b : Nat)
    (h : BB429ForcedNormalize.forcedExcluded a b = true) :
    ∀ n, BB429SourceLadder.sourceRun n highLevelStart ≠ some (.J a b) := by
  intro n hn
  have hl : BB429.run n (0,0)=some (a,b) :=
    BB429SourceMod16.source_run_to_local n a b hn
  exact (BB429ForcedNormalize.forcedExcluded_sound a b h n) hl

#print axioms source_forcedExcluded_sound
end BB429SourceForcedNormalize
