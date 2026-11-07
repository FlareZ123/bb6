import SourceRawHalt38
import BB429Combined686

/-!
All 686 affine/inverse genuine-root terminal exclusions transported through
the established, unchanged Google DeepMind original-raw six-state Cryptids
source bridge. The result is an exact raw halting equivalence still containing
the authentic terminal witness quantifier, not a machine decision.
-/
namespace BB429Actual686
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

theorem source_halt_not_686 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%262144 ∉ BB429Combined686.excluded686 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429Combined686.blank_halt_not_686 n u w hl hg

/-- An exact raw six-state halting characterization with the combined
    686 residue exclusions. It does not assert existence of n,u,w. -/
theorem raw_halts_iff_686 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 ∧
        u%262144 ∉ BB429Combined686.excluded686 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩ :=
      BB429ActualHalt38.raw_halts_iff_38_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      source_halt_not_686 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,_⟩
    exact BB429ActualHalt38.raw_halts_iff_38_gates.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩

#print axioms source_halt_not_686
#print axioms raw_halts_iff_686
end BB429Actual686
