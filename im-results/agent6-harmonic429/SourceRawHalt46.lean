import SourceRawHalt1024
import SourceRawHaltNo253

namespace BB429ActualHalt46
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Collaborative sharpening of the exact source-native raw halting
    criterion: combines Agent 6's 125-mod1024 exclusion with Agent 18's
    independently derived 253-mod1024 exclusion. The 46 surviving
    modulo-1024 classes are necessary only; their root reachability
    remains completely open. -/
theorem raw_halts_iff_46_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask⟩ :=
      BB429ActualHalt1024.raw_halts_iff_47_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,
      BB429SourceNo253.source_halting_not_253_mod1024 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253⟩
    apply BB429ActualHalt1024.raw_halts_iff_47_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask⟩

#print axioms raw_halts_iff_46_gates
end BB429ActualHalt46
