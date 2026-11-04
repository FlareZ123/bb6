import SourceRawHalt40
import BB429No137mod1024
import BB429No521mod1024
namespace BB429ActualHalt38
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
theorem source_no137 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%1024≠137 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No137mod1024.blank_halt_not_137_mod1024 n u w hl hg
theorem source_no521 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%1024≠521 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No521mod1024.blank_halt_not_521_mod1024 n u w hl hg
/-- Original source halting iff genuine terminal belongs to 38 of 1024 classes. -/
theorem raw_halts_iff_38_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265⟩ :=
      BB429ActualHalt40.raw_halts_iff_40_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,
      source_no137 n u w hr hn, source_no521 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩
    apply BB429ActualHalt40.raw_halts_iff_40_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265⟩
#print axioms raw_halts_iff_38_gates
end BB429ActualHalt38
