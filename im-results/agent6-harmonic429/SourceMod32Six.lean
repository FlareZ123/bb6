import SourceMod32
import BB429Mod32Six
import Lean.Elab.Tactic.Omega

namespace BB429SourceMod32Six
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Necessary six-residue modular restriction on real blank-entry high-level
    halting configurations, transported through the unchanged native Cryptids
    accelerated transition equality. -/
theorem source_halting_mod32_six (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%32=3 ∨ u%32=9 ∨ u%32=17 ∨ u%32=21 ∨ u%32=25 ∨ u%32=29 := by
  exact BB429Mod32Six.blank_halting_mod32_six n u w
    (BB429SourceMod16.source_run_to_local n u w h)
    (BB429SourceMod16.source_next_none_to_local u w hn)

#print axioms source_halting_mod32_six
end BB429SourceMod32Six
