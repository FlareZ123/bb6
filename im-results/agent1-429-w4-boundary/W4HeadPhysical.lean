import W4HeadPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429W4HeadPhysical

open BB6Coverage BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429PhysicalFrontier BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429W4HeadMax BB429W4HeadPrefix

/-- Physical raw-machine right-head barrier for the complete parameter-uniform
source E/1 return: at every primitive prefix up to the first revisit, the
head position is no farther right than its entry coordinate. This includes
all intermediate F/B/C/A states and the return itself, and is valid from
any raw configuration representing the stated source S_E tape family. -/
theorem physical_sourceScanE_all_prefixes_right_bound
    (b t : Nat) (suffix : List Bool) (c : Config)
    (hrep : Represents (sourceScanE b suffix) c)
    (ht : t ≤ crossTime b + 1) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 t c = some c' ∧
      c'.head ≤ c.head := by
  have hfull := sourceScanE_e1_revisit_delta b suffix
  have hlen : crossTime b+1 = t+(crossTime b+1-t) := by omega
  cases hpre : runWithDelta t (sourceScanE b suffix) with
  | none =>
      rw [hlen, runWithDelta_add, hpre] at hfull
      simp at hfull
  | some p =>
      have hloc : p.2 ≤ 0 :=
        sourceScanE_delta_all_prefixes_le_zero b t suffix ht p.1 p.2 hpre
      obtain ⟨c', hraw, hnew, hhead⟩ :=
        source_runWithDelta_rep t (sourceScanE b suffix) c hrep p.1 p.2 hpre
      refine ⟨c', hraw, ?_⟩
      omega

#print axioms physical_sourceScanE_all_prefixes_right_bound

end BB429W4HeadPhysical
