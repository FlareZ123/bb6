import SourceRawHaltNo253
import SourceRawHalt46
import BB429No381
import Lean.Elab.Tactic.Omega

namespace BB429SourceNo381
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

theorem source_halting_not_381_mod1024 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%1024 ≠ 381 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No381.blank_halt_mod1024_ne_381 n u w hl hg

/-- Genuine original raw halting iff reaching a six-lift terminal outside two
    provably blank-unreachable strict subfamilies of the 125 modulo128 sector. -/
theorem raw_halts_iff_six_lifts_without_253_381 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨ u%128=125) ∧
        u%1024 ≠ 253 ∧ u%1024 ≠ 381 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hcond,hnot⟩ :=
      BB429SourceNo253.raw_halts_iff_six_lifts_without_253.mp h
    exact ⟨n,u,w,hr,hn,hcond,hnot,source_halting_not_381_mod1024 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hcond,hnot253,hnot381⟩
    apply BB429SourceNo253.raw_halts_iff_six_lifts_without_253.mpr
    exact ⟨n,u,w,hr,hn,hcond,hnot253⟩


/-- Collaborative 45-class exact raw halt reduction modulo 1024. All 45
    remaining residues are necessary, and none is asserted reachable. -/
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
    obtain ⟨n,u,w,hr,hn,hmask,h253⟩ :=
      BB429ActualHalt46.raw_halts_iff_46_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,
      source_halting_not_381_mod1024 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381⟩
    apply BB429ActualHalt46.raw_halts_iff_46_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253⟩

#print axioms raw_halts_iff_45_gates
#print axioms source_halting_not_381_mod1024
#print axioms raw_halts_iff_six_lifts_without_253_381
end BB429SourceNo381
