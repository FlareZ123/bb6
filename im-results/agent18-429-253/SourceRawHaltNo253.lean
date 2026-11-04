import SourceRawHaltRefined
import BB429No253
import Lean.Elab.Tactic.Omega

namespace BB429SourceNo253
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- The exact genuine-blank source acceleration excludes the whole 253 modulo 1024
    first-counter sector on its unique halting line. -/
theorem source_halting_not_253_mod1024 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%1024 ≠ 253 := by
  have hl : BB429.run n (0,0) = some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No253.blank_halt_mod1024_ne_253 n u w hl hg

/-- Strict strengthening of the pinned raw-TM six-lift equivalence.
    No surviving class is thereby certified reachable or unreachable. -/
theorem raw_halts_iff_six_lifts_without_253 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨ u%128=125) ∧
        u%1024 ≠ 253 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hcond⟩ :=
      BB429ActualHaltRefined.raw_halts_iff_refined_gates.mp h
    exact ⟨n,u,w,hr,hn,hcond,source_halting_not_253_mod1024 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hcond,hnot⟩
    apply BB429ActualHaltRefined.raw_halts_iff_refined_gates.mpr
    exact ⟨n,u,w,hr,hn,hcond⟩

#print axioms source_halting_not_253_mod1024
#print axioms raw_halts_iff_six_lifts_without_253
end BB429SourceNo253
