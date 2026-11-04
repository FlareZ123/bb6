import SourceRawHalt44
import BB429No1661mod2048
import BB429No893mod2048
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt86
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- A further native-source obstruction for a rooted accelerated terminal
    in the previously surviving 637 mod 1024 sector. -/
theorem source_halt_not_1661_mod2048 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%2048≠1661 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No1661mod2048.blank_halt_not_1661_mod2048 n u w hl hg

/-- A second disjoint rooted obstruction in the surviving 893 mod1024 sector. -/
theorem source_halt_not_893_mod2048 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%2048≠893 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No893mod2048.blank_halt_not_893_mod2048 n u w hl hg

/-- Genuine raw-source halting is reduced to 86 necessary residue
    classes modulo 2048. These classes are not known reachable. -/
theorem raw_halts_iff_86_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%2048≠1661 ∧ u%2048≠893 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509⟩ :=
      BB429ActualHalt44.raw_halts_iff_44_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,
      source_halt_not_1661_mod2048 n u w hr hn,
      source_halt_not_893_mod2048 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893⟩
    apply BB429ActualHalt44.raw_halts_iff_44_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509⟩

#print axioms source_halt_not_1661_mod2048
#print axioms source_halt_not_893_mod2048
#print axioms raw_halts_iff_86_gates
end BB429ActualHalt86
