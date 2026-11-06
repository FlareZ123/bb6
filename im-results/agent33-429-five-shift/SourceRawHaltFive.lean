import SourceRawHaltManyLifts
import BB429FiveShift

namespace BB429ActualFiveShift
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- The actual unchanged six-state Cryptids machine cannot visit any of
    these five terminal families from its authentic blank start. -/
theorem source_halt_not_five (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u % 16384 ∉ BB429FiveShift.excludedFive := by
  have hl : BB429.run n (0,0) = some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429FiveShift.blank_halt_not_five n u w hl hg

/-- Original raw-Turing machine halting iff there is a genuinely reached
    terminal witness satisfying both previously certified modulo constraints
    and the five additional full 16-bit cylinder exclusions. -/
theorem raw_halts_iff_38_plus_45 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 ∧
        u%16384 ∉ BB429ManyLifts.newLifts ∧
        u%16384 ∉ BB429FiveShift.excludedFive := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,h40⟩ :=
      BB429ActualManyLifts.raw_halts_iff_38_plus_40.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h40, source_halt_not_five n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,h40,_⟩
    exact BB429ActualManyLifts.raw_halts_iff_38_plus_40.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,h40⟩

#print axioms source_halt_not_five
#print axioms raw_halts_iff_38_plus_45
end BB429ActualFiveShift
