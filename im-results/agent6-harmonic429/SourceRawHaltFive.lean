import SourceRawHaltIff
import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429ActualHaltFive
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- The exact original Cryptids accelerated blank orbit cannot stop at any
    u divisible by 4 with remainder 3. -/
theorem source_halt_not_three_mod_four (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%4 ≠ 3 := by
  exact BB429NoThree.blank_halt_not_three_mod_four n u w
    (BB429SourceMod16.source_run_to_local n u w h)
    (BB429SourceMod16.source_next_none_to_local u w hn)

/-- All remaining genuine blank-root accelerated halts require one of
    five u classes modulo 32. The surviving cases are not proved reachable. -/
theorem source_halting_five (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%32=9 ∨ u%32=17 ∨ u%32=21 ∨ u%32=25 ∨ u%32=29 := by
  have h6 := BB429SourceMod32Six.source_halting_mod32_six n u w h hn
  have h3 := source_halt_not_three_mod_four n u w h hn
  omega

/-- Genuine raw six-state blank-tape halting is equivalent to reachability
    of one of five remaining halting junction classes. This remains a
    decision problem over infinitely many source states. -/
theorem raw_halts_iff_five_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%32=9 ∨ u%32=17 ∨ u%32=21 ∨ u%32=25 ∨ u%32=29) := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hs,_⟩ :=
      BB429ActualHaltIff.raw_halts_iff_six_gates.mp h
    exact ⟨n,u,w,hr,hs,source_halting_five n u w hr hs⟩
  · rintro ⟨n,u,w,hr,hs,h5⟩
    apply BB429ActualHaltIff.raw_halts_iff_six_gates.mpr
    refine ⟨n,u,w,hr,hs,?_⟩
    omega

#print axioms source_halt_not_three_mod_four
#print axioms source_halting_five
#print axioms raw_halts_iff_five_gates
end BB429ActualHaltFive
