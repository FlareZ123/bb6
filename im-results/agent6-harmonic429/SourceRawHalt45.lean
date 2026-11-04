import SourceRawHalt46
import BB429No381mod1024
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt45
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Pinned-native Cryptids acceleration cannot halt in 381 mod1024. -/
theorem source_halt_not_381_mod1024 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%1024≠381 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No381mod1024.blank_halt_not_381_mod1024 n u w hl hg

/-- Agents 6 and 18 jointly eliminate three out of eight subfamilies
    of terminal 125 modulo128. The 45 classes are necessary candidate
    gates only, with no halt witness or complete machine decision. -/
theorem raw_halts_iff_45_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hcond,h253⟩ :=
      BB429ActualHalt46.raw_halts_iff_46_gates.mp h
    exact ⟨n,u,w,hr,hn,hcond,h253,
      source_halt_not_381_mod1024 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hcond,h253,h381⟩
    apply BB429ActualHalt46.raw_halts_iff_46_gates.mpr
    exact ⟨n,u,w,hr,hn,hcond,h253⟩

#print axioms source_halt_not_381_mod1024
#print axioms raw_halts_iff_45_gates
end BB429ActualHalt45
