import SourceRawHalt42
import BB429No265mod512
import Lean.Elab.Tactic.Omega
namespace BB429ActualHalt40
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
theorem source_halt_not_265_mod512 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%512≠265 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No265mod512.blank_halt_not_265_mod512 n u w hl hg
/-- A necessary 40/1024-class gate for genuine raw #429 halting. -/
theorem raw_halts_iff_40_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393⟩ :=
      BB429ActualHalt42.raw_halts_iff_42_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,
      source_halt_not_265_mod512 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265⟩
    apply BB429ActualHalt42.raw_halts_iff_42_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393⟩
#print axioms source_halt_not_265_mod512
#print axioms raw_halts_iff_40_gates
end BB429ActualHalt40
