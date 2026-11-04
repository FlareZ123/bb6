import SourceRawHaltFive
import BB429NoTwentyFive
import Lean.Elab.Tactic.Omega

namespace BB429ActualHaltFour
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Exact source-semantics exclusion of u=25 mod32 terminal states. -/
theorem source_halt_not_twentyfive (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%32 ≠ 25 := by
  exact BB429NoTwentyFive.blank_halt_not_twentyfive n u w
    (BB429SourceMod16.source_run_to_local n u w h)
    (BB429SourceMod16.source_next_none_to_local u w hn)

/-- Four all-time necessary halting classes modulo 32 on the true root. -/
theorem source_halting_four (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%32=9 ∨ u%32=17 ∨ u%32=21 ∨ u%32=29 := by
  have h5 := BB429ActualHaltFive.source_halting_five n u w h hn
  have h25 := source_halt_not_twentyfive n u w h hn
  omega

/-- Genuine six-state raw-machine halting is equivalent to blank-orbit
    reachability of one of four remaining classes. No halt witness or
    nonhalting conclusion is implied for these surviving classes. -/
theorem raw_halts_iff_four_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%32=9 ∨ u%32=17 ∨ u%32=21 ∨ u%32=29) := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hs,_⟩ :=
      BB429ActualHaltFive.raw_halts_iff_five_gates.mp h
    exact ⟨n,u,w,hr,hs,source_halting_four n u w hr hs⟩
  · rintro ⟨n,u,w,hr,hs,h4⟩
    apply BB429ActualHaltFive.raw_halts_iff_five_gates.mpr
    refine ⟨n,u,w,hr,hs,?_⟩
    omega

#print axioms source_halt_not_twentyfive
#print axioms source_halting_four
#print axioms raw_halts_iff_four_gates
end BB429ActualHaltFour
