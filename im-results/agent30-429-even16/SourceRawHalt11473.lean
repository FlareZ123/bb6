import SourceRawHalt38
import BB429No11473mod16384

namespace BB429ActualHalt16384
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- The new genuine-blank-root infinite-cylinder exclusion transported
into the pinned, unchanged Google DeepMind Cryptids raw six-state machine. -/
theorem source_no_11473_mod16384 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) : u%16384≠11473 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No11473.blank_halt_not_11473_mod16384 n u w hl hg

/-- Source-level halting equivalence strengthens the published 38/1024
necessary terminal mask. It retains true-root existential reachability. -/
theorem raw_halts_iff_38_gates_and_new_cylinder :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%16384≠11473 ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩ :=
      BB429ActualHalt38.raw_halts_iff_38_gates.mp h
    exact ⟨n,u,w,hr,hn,source_no_11473_mod16384 n u w hr hn,
      hmask,h253,h381,h509,h393,h265,h137,h521⟩
  · rintro ⟨n,u,w,hr,hn,hnew,hmask,h253,h381,h509,h393,h265,h137,h521⟩
    exact BB429ActualHalt38.raw_halts_iff_38_gates.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩

#print axioms source_no_11473_mod16384
#print axioms raw_halts_iff_38_gates_and_new_cylinder
end BB429ActualHalt16384
