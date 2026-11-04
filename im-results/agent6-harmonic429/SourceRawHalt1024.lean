import SourceRawHaltRefined
import BB429No125mod1024
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt1024
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Source-native exclusion for the entire 125-mod1024 terminal family. -/
theorem source_halt_not_125_mod1024 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%1024≠125 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No125mod1024.blank_halt_not_125_mod1024 n u w hl hg

/-- Genuine raw Cryptids-machine halting iff the true blank macro orbit
    reaches one of the remaining 47 modulo-1024 terminal residue classes.
    This is a necessary-gate equivalence, NOT a decision or halt witness. -/
theorem raw_halts_iff_47_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask⟩ :=
      BB429ActualHaltRefined.raw_halts_iff_refined_gates.mp h
    have h125 := source_halt_not_125_mod1024 n u w hr hn
    refine ⟨n,u,w,hr,hn,?_⟩
    omega
  · rintro ⟨n,u,w,hr,hn,hmask⟩
    apply BB429ActualHaltRefined.raw_halts_iff_refined_gates.mpr
    refine ⟨n,u,w,hr,hn,?_⟩
    omega

#print axioms source_halt_not_125_mod1024
#print axioms raw_halts_iff_47_gates
end BB429ActualHalt1024
