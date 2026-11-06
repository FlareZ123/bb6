import SourceRawHalt38
import BB429ManyLifts

namespace BB429ActualManyLifts
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Every genuine original Cryptids blank-root terminal avoids the forty
    new 16-bit cylinders. -/
theorem source_halt_not_new_lifts (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%16384 ∉ BB429ManyLifts.newLifts := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429ManyLifts.blank_halt_not_new_lifts n u w hl hg

/-- The unchanged original Cryptids raw machine's exact halting condition,
    refined by the forty additional genuine-root exclusions. The existential
    terminal witness remains explicit; no surviving class is claimed reached. -/
theorem raw_halts_iff_38_plus_40 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 ∧
        u%16384 ∉ BB429ManyLifts.newLifts := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩ :=
      BB429ActualHalt38.raw_halts_iff_38_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      source_halt_not_new_lifts n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,_⟩
    exact BB429ActualHalt38.raw_halts_iff_38_gates.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩

#print axioms source_halt_not_new_lifts
#print axioms raw_halts_iff_38_plus_40
end BB429ActualManyLifts
