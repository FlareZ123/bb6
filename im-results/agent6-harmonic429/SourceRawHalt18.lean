import SourceRawHalt38
import BB429GateArithmetic
import BB429No329mod512
import BB429NewSix
import BB429No81mod512
import BB429NextSeven
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt18
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Original source blank section terminal satisfies every new exact
    all-time rooted inverse certificate, uniformly in its counters. -/
theorem source_fresh (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    BB429GateArithmetic.newForbidden u := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact ⟨BB429No81.blank_halt_not_81_mod512 n u w hl hg,
    BB429NewSix.blank_halt_not_309_mod512 n u w hl hg,
    BB429No329.blank_halt_not_329_mod512 n u w hl hg,
    BB429NewSix.blank_halt_not_373_mod512 n u w hl hg,
    BB429NewSix.blank_halt_not_457_mod512 n u w hl hg,
    BB429NewSix.blank_halt_not_501_mod512 n u w hl hg,
    BB429NewSix.blank_halt_not_181_mod1024 n u w hl hg,
    BB429NextSeven.blank_halt_not_437_mod1024 n u w hl hg,
    BB429NextSeven.blank_halt_not_585_mod1024 n u w hl hg,
    BB429NextSeven.blank_halt_not_629_mod1024 n u w hl hg,
    BB429NextSeven.blank_halt_not_693_mod1024 n u w hl hg,
    BB429NextSeven.blank_halt_not_713_mod1024 n u w hl hg,
    BB429NextSeven.blank_halt_not_757_mod1024 n u w hl hg,
    BB429NextSeven.blank_halt_not_977_mod1024 n u w hl hg⟩

/-- Exact raw six-state machine halting iff a true original source
    blank-root terminal belongs to precisely the 18 surviving modular classes.
    No such terminal is asserted reachable. -/
theorem raw_halts_iff_18_gates :
    IsHalt target ↔
    ∃ n u w,
      BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
      highLevelNext (.J u w) = none ∧
      BB429GateArithmetic.gate18 u := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩ :=
      BB429ActualHalt38.raw_halts_iff_38_gates.mp h
    have hbase : BB429GateArithmetic.old38 u :=
      ⟨hmask,h253,h381,h509,h393,h265,h137,h521⟩
    have hfresh := source_fresh n u w hr hn
    have hgate :=
      (BB429GateArithmetic.old38_and_fresh_iff_gate18 u).mp ⟨hbase,hfresh⟩
    exact ⟨n,u,w,hr,hn,hgate⟩
  · rintro ⟨n,u,w,hr,hn,hgate⟩
    have hbase :=
      ((BB429GateArithmetic.old38_and_fresh_iff_gate18 u).mpr hgate).1
    rcases hbase with ⟨hmask,h253,h381,h509,h393,h265,h137,h521⟩
    exact BB429ActualHalt38.raw_halts_iff_38_gates.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩

#print axioms source_fresh
#print axioms raw_halts_iff_18_gates
end BB429ActualHalt18
