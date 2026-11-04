import SourceRawHaltNo381
import BB429No509
import Lean.Elab.Tactic.Omega

namespace BB429SourceNo509
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

theorem source_halting_not_509_mod1024 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%1024 ≠ 509 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No509.blank_halt_mod1024_ne_509 n u w hl hg

/-- Exact original raw-machine halting iff the genuine blank macro orbit
    enters one of 44 remaining necessary modulo-1024 halt sectors. -/
theorem raw_halts_iff_44_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381⟩ :=
      BB429SourceNo381.raw_halts_iff_45_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,
      source_halting_not_509_mod1024 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509⟩
    apply BB429SourceNo381.raw_halts_iff_45_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381⟩

#print axioms source_halting_not_509_mod1024
#print axioms raw_halts_iff_44_gates
end BB429SourceNo509
