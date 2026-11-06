import SourceRawHalt38
import BB429SplitSieve

namespace BB429ActualSplitSieve
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Unmodified original high-level Cryptids root is subject to the
    673 new all-quotient inverse exclusions. -/
theorem source_halt_not_673 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u % 262144 ∉ BB429SplitSieve.excluded := by
  have hl : BB429.run n (0,0) = some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429SplitSieve.blank_halt_not_excluded n u w hl hg

/-- The unchanged upstream original machine halts iff a genuinely
    reached source terminal satisfies the former 38/1024 necessary
    conditions and the new 673-class exclusion. This equivalence does
    not assert the existence of a terminal witness. -/
theorem raw_halts_iff_38_plus_673 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 ∧
        u%262144 ∉ BB429SplitSieve.excluded := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩ :=
      BB429ActualHalt38.raw_halts_iff_38_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      source_halt_not_673 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,_⟩
    exact BB429ActualHalt38.raw_halts_iff_38_gates.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩

#print axioms source_halt_not_673
#print axioms raw_halts_iff_38_plus_673
end BB429ActualSplitSieve
