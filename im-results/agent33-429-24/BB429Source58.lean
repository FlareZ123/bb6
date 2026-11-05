import BB429Gate24Class
import BB429Inverse38

namespace BB429Source58
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Entire 8192 terminal cylinders are excluded from genuine original-machine
    halting witnesses by a mechanically checked inverse-tree certificate. -/
theorem source_halt_excludes38 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%8192 ∉ BB429Kernel.excluded38 := by
  intro hm
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429Kernel.blank_no_halt_38 n u w (u%8192) hl hg rfl hm

/-- A raw-TM criterion retaining the actual source terminal witness,
    and excluding thirty-eight complete modulo-8192 cylinders. -/
theorem raw_halts_iff_58_constraints :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%2048 ∈ BB429Final24.liveClasses ∧
        u%8192 ∉ BB429Kernel.excluded38 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hl⟩ := BB429Final24.raw_halts_iff_24_classes.mp h
    exact ⟨n,u,w,hr,hn,hl,source_halt_excludes38 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hl,_⟩
    exact BB429Final24.raw_halts_iff_24_classes.mpr ⟨n,u,w,hr,hn,hl⟩

#print axioms source_halt_excludes38
#print axioms raw_halts_iff_58_constraints
end BB429Source58
