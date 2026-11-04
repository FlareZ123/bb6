import SourceRawHalt1021Five
import BB429No1021Six
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt1021Six
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- In the pinned original Cryptids accelerator, all six new entire
1021-mod-1024 lifts are ruled out on every genuine blank-reachable
terminal section, with no time bound. -/
theorem source_halt_not_six_1021 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%16384≠2045 ∧ u%16384≠4093 ∧ u%16384≠9213 ∧
      u%16384≠10237 ∧ u%16384≠11261 ∧ u%16384≠12285 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No1021Six.blank_halt_not_six_1021_lifts n u w hl hg

/-- Exact original raw machine halting iff a true blank-root source terminal
satisfies the previously verified 86/2048 mask and all six exclusions.
Surviving residue classes are necessary, not proven reachable. -/
theorem raw_halts_iff_86_plus_six :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%2048≠1661 ∧ u%2048≠893 ∧
        u%16384≠9213 ∧ u%16384≠11261 ∧ u%16384≠12285 ∧
        u%16384≠4093 ∧ u%16384≠10237 ∧ u%16384≠2045 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237⟩ :=
        BB429ActualHalt1021Five.raw_halts_iff_86_plus_five.mp h
    obtain ⟨h2045,_,_,_,_,_⟩ :=
      source_halt_not_six_1021 n u w hr hn
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237,h2045⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237,h2045⟩
    apply BB429ActualHalt1021Five.raw_halts_iff_86_plus_five.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237⟩

#print axioms source_halt_not_six_1021
#print axioms raw_halts_iff_86_plus_six

end BB429ActualHalt1021Six
