import SourceRawHalt44
import BB429No393mod512
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt42
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- A true blank-start terminal of the original Cryptids accelerator
    cannot lie in either 393 or 905 modulo1024. -/
theorem source_halt_not_393_mod512 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%512≠393 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No393mod512.blank_halt_not_393_mod512 n u w hl hg

/-- Exact original-machine halt iff authentic blank-root high-level terminal
    belongs to at most 42 surviving first-counter classes modulo1024. -/
theorem raw_halts_iff_42_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509⟩ :=
      BB429ActualHalt44.raw_halts_iff_44_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,
      source_halt_not_393_mod512 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393⟩
    apply BB429ActualHalt44.raw_halts_iff_44_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509⟩

#print axioms source_halt_not_393_mod512
#print axioms raw_halts_iff_42_gates
end BB429ActualHalt42
