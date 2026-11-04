import SourceMod16
import BB429Extra19
import Lean.Elab.Tactic.Omega

namespace BB429SourceMod32
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Two-stage blank-root modular restriction on genuine Cryptids highLevelNext.
This excludes u ≡ 19 mod 32 beyond the mod16 exclusion, and preserves
the exact original-machine source transfer hypotheses. -/
theorem source_halting_mod32 (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%32=1 ∨ u%32=3 ∨ u%32=5 ∨ u%32=9 ∨ u%32=13 ∨
    u%32=17 ∨ u%32=21 ∨ u%32=25 ∨ u%32=29 := by
  exact BB429Extra19.blank_halting_mod32 n u w
    (BB429SourceMod16.source_run_to_local n u w h)
    (BB429SourceMod16.source_next_none_to_local u w hn)

#print axioms source_halting_mod32
end BB429SourceMod32
