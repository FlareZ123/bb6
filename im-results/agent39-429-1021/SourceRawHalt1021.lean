import SourceRawHalt86
import BB429No1021More
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt1021
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- A genuine pinned Cryptids high-level terminal cannot have one of the
three new 1021 (mod1024) lifts. This uses the exact source-to-local bridge. -/
theorem source_halt_not_three_1021 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%16384 ≠ 9213 ∧ u%16384 ≠ 11261 ∧ u%16384 ≠ 12285 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No1021.blank_halt_not_three_1021_lifts n u w hl hg

/-- A necessary-gate equivalence for the genuine original raw six-state TM.
The counter gate conditions are only necessary possibilities and their
existential reachability remains unresolved. -/
theorem raw_halts_iff_86_plus_three :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%2048≠1661 ∧ u%2048≠893 ∧
        u%16384≠9213 ∧ u%16384≠11261 ∧ u%16384≠12285 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893⟩ :=
      BB429ActualHalt86.raw_halts_iff_86_gates.mp h
    obtain ⟨h9213,h11261,h12285⟩ :=
      source_halt_not_three_1021 n u w hr hn
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,h9213,h11261,h12285⟩
    apply BB429ActualHalt86.raw_halts_iff_86_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893⟩

#print axioms source_halt_not_three_1021
#print axioms raw_halts_iff_86_plus_three

end BB429ActualHalt1021
