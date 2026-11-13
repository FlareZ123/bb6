import Low42RootNoFatal
import W4HeadPrefix
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

namespace BB429Low42RootMax

open BB6Coverage BB6Bubble
open BB429OddExcursion BB429SourceE1Delta
open BB429W4HeadMax BB429W4HeadPrefix
open BB429PhysicalBridge BB429Low42RootNoFatal

/-- Exact full-prefix head monitor for the authentic low42 root suffix.
    The maximum rightward displacement is 30, attained during this
    1,077-step Junc(53,0,20) -> Junc(0,0,136) run. -/
theorem low42_root_source_head_max :
    runWithMax 1077 rootLow42Start =
      some (rootLow42End, -109, 30) := by
  decide

/-- Lift the source maximum monitor to the original six-state physical
    machine. Every primitive prefix stays at or left of entry-head +30,
    and the endpoint displacement is exactly -109. -/
theorem low42_root_physical_head_bound
    (c : Config) (hrep : Represents rootLow42Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 1077 c = some d ∧
      Represents rootLow42End d ∧
      (∀ t : Nat, t ≤ 1077 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          e.head ≤ c.head + (30 : Int)) ∧
      d.head = c.head - (109 : Int) := by
  have hfull := low42_root_source_head_max
  have hdelta :
      runWithDelta 1077 rootLow42Start =
        some (rootLow42End, -109) := by
    have hproj := runWithMax_toDelta 1077 rootLow42Start
    rw [hfull] at hproj
    exact hproj.symm
  obtain ⟨d,hraw,hrepD,hhead⟩ :=
    source_runWithDelta_rep 1077 rootLow42Start c hrep
      rootLow42End (-109) hdelta
  have hprefix :
      ∀ t : Nat, t ≤ 1077 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          e.head ≤ c.head + (30 : Int) := by
    intro t ht
    cases hpre : runWithMax t rootLow42Start with
    | none =>
        have hlen : t+(1077-t)=1077 := by omega
        rw [← hlen, runWithMax_add, hpre] at hfull
        simp at hfull
    | some p =>
        have hbound :=
          runWithMax_prefix_le t (1077-t) rootLow42Start p hpre
            (rootLow42End,-109,30) hfull
        have hdeltaPrefix :
            runWithDelta t rootLow42Start = some (p.1,p.2.1) := by
          have hproj := runWithMax_toDelta t rootLow42Start
          rw [hpre] at hproj
          exact hproj.symm
        obtain ⟨e,he,hrepE,hheadE⟩ :=
          source_runWithDelta_rep t rootLow42Start c hrep
            p.1 p.2.1 hdeltaPrefix
        refine ⟨e,he,?_⟩
        change e.head = c.head + p.2.1 at hheadE
        omega
  have hheadFinal : d.head = c.head - (109 : Int) := by
    change d.head = c.head + (-109) at hhead
    omega
  exact ⟨d,hraw,hrepD,hprefix,hheadFinal⟩

#print axioms low42_root_source_head_max
#print axioms low42_root_physical_head_bound

end BB429Low42RootMax
