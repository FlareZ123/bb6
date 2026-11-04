import SourceRawHalt1021Six
import BB429No1021Eight
import Lean.Elab.Tactic.Omega

namespace BB429ActualHalt1021Eight
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Eight new entire congruence cylinders, each impossible at an actual
blank-origin terminal in the pinned unchanged Cryptids source machine. -/
theorem source_halt_not_eight_1021 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%16384≠1021 ∧ u%16384≠2045 ∧ u%16384≠3069 ∧
      u%16384≠4093 ∧ u%16384≠9213 ∧ u%16384≠10237 ∧
      u%16384≠11261 ∧ u%16384≠12285 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No1021Eight.blank_halt_not_eight_1021_lifts n u w hl hg

/-- Raw machine halting is iff a genuinely blank-root original
Cryptids high-level terminal satisfies the previous 86/2048 mask
and all eight new quantified exclusions. Necessary gates are not
asserted to be reachable or sufficient. -/
theorem raw_halts_iff_86_plus_eight :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%2048≠1661 ∧ u%2048≠893 ∧
        u%16384≠9213 ∧ u%16384≠11261 ∧ u%16384≠12285 ∧
        u%16384≠4093 ∧ u%16384≠10237 ∧ u%16384≠2045 ∧
        u%16384≠1021 ∧ u%16384≠3069 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237,h2045⟩ :=
        BB429ActualHalt1021Six.raw_halts_iff_86_plus_six.mp h
    obtain ⟨h1021,_,h3069,_,_,_,_,_⟩ :=
      source_halt_not_eight_1021 n u w hr hn
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237,h2045,h1021,h3069⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237,h2045,h1021,h3069⟩
    apply BB429ActualHalt1021Six.raw_halts_iff_86_plus_six.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h1661,h893,
      h9213,h11261,h12285,h4093,h10237,h2045⟩

#print axioms source_halt_not_eight_1021
#print axioms raw_halts_iff_86_plus_eight

end BB429ActualHalt1021Eight
