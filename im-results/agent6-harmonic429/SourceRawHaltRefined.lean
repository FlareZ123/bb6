import SourceRawHaltFour
import BB429Deep17
import BB429TwentyOne
import BB429NoTwentyNine128
import BB429NoNinetyThree128
import Lean.Elab.Tactic.Omega

namespace BB429ActualHaltRefined
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Source-connected sharpening for two congruence sectors and a deeper
    residual 17-sector. No claim of reaching any remaining gate is made. -/
theorem source_halt_refined (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%64=9 ∨ u%128=81 ∨ u%64=53 ∨ (u%32=29 ∧ u%128≠29 ∧ u%128≠93) := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  have h4 := BB429ActualHaltFour.source_halting_four n u w hr hn
  have h41 := BB429NewGate.no_blank_halt_41_mod64 n u w hl hg
  have h49 := BB429NewGate.no_blank_halt_49_mod64 n u w hl hg
  have h21 := BB429TwentyOne.blank_no_twentyone_mod64 n u w hl hg
  have h29 := BB429NoTwentyNine128.blank_halt_not_29_mod128 n u w hl hg
  have h93 := BB429NoNinetyThree128.blank_halt_not_93_mod128 n u w hl hg
  by_cases h17 : u%32=17
  · exact Or.inr (Or.inl (BB429Deep17.blank_17_sector_must_81 n u w hl hg h17))
  · omega

/-- Exact raw halting criterion with 7 modulo-128 residue lifts. -/
theorem raw_halts_iff_refined_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨ (u%32=29 ∧ u%128≠29 ∧ u%128≠93)) := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,_⟩ := BB429ActualHaltFour.raw_halts_iff_four_gates.mp h
    exact ⟨n,u,w,hr,hn,source_halt_refined n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hcond⟩
    apply BB429ActualHaltFour.raw_halts_iff_four_gates.mpr
    refine ⟨n,u,w,hr,hn,?_⟩
    omega

#print axioms source_halt_refined
#print axioms raw_halts_iff_refined_gates
end BB429ActualHaltRefined
