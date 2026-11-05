import BB429Gate24Class
import BB429New9Lift

namespace BB429Source9Lift
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Transport the all-time, entire 4105(mod8192) exclusion from the exact
    local section accelerator to the unchanged original six-state machine. -/
theorem source_halt_not_4105 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%8192≠4105 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429New9Lift.no_halting_2_mod8192 n u w hl hg

theorem source_halt_not_6153 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%8192≠6153 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429New9Lift.no_halting_3_mod8192 n u w hl hg

/-- A real raw-machine halting witness must satisfy the 24 classes modulo
    2048 and both new complete 8192-cylinder exclusions. The converse
    only uses the real source terminal witness, never a hypothetical gate. -/
theorem raw_halts_iff_94_candidates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%2048 ∈ BB429Final24.liveClasses ∧
        u%8192≠4105 ∧ u%8192≠6153 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hl⟩ :=
      BB429Final24.raw_halts_iff_24_classes.mp h
    exact ⟨n,u,w,hr,hn,hl,
      source_halt_not_4105 n u w hr hn,
      source_halt_not_6153 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hl,h4105,h6153⟩
    exact BB429Final24.raw_halts_iff_24_classes.mpr
      ⟨n,u,w,hr,hn,hl⟩

#print axioms source_halt_not_4105
#print axioms source_halt_not_6153
#print axioms raw_halts_iff_94_candidates
end BB429Source9Lift
