import SourceRawHaltSplit
import BB429ShiftRays

namespace BB429ActualShiftSieve
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- The four new affine-cylinder restrictions apply directly to the
    unchanged original Cryptids high-level blank-root machine. -/
theorem source_halt_not_four (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%32768≠765 ∧ u%32768≠3281 ∧
    u%262144≠2385 ∧ u%131072≠16381 := by
  have hl : BB429.run n (0,0) = some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact ⟨BB429ShiftRays.blank_halt_not_765_mod_32768 n u w hl hg,
    BB429ShiftRays.blank_halt_not_3281_mod_32768 n u w hl hg,
    BB429ShiftRays.blank_halt_not_2385_mod_262144 n u w hl hg,
    BB429ShiftRays.blank_halt_not_16381_mod_131072 n u w hl hg⟩

/-- The raw six-state machine can halt only through the still-unresolved
    authentic terminal events passing the earlier 673 exclusions and
    all four new infinite-cylinder exclusions. This equivalence makes
    no assertion that such an event exists. -/
theorem raw_halts_iff_673_plus_four :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 ∧
        u%262144 ∉ BB429SplitSieve.excluded ∧
        u%32768≠765 ∧ u%32768≠3281 ∧
        u%262144≠2385 ∧ u%131072≠16381 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,h673⟩ :=
      BB429ActualSplitSieve.raw_halts_iff_38_plus_673.mp h
    obtain ⟨h765,h3281,h2385,h16381⟩ :=
      source_halt_not_four n u w hr hn
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h673,h765,h3281,h2385,h16381⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,
      h137,h521,h673,_,_,_,_⟩
    exact BB429ActualSplitSieve.raw_halts_iff_38_plus_673.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,h673⟩

#print axioms source_halt_not_four
#print axioms raw_halts_iff_673_plus_four
end BB429ActualShiftSieve
