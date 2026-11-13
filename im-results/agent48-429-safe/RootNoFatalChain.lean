import RootNoFatalPhysical
import RootOuterLow42NoFatal
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429RootNoFatalChain

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429NoFatalGuard BB429RootNoFatalPrefix
open BB429RootNoFatalPhysical BB429RootOuterLow42NoFatal BB429FinishScanEDelta

/-- Compose the source-checked blank-root prefix with the existing
    physical outer-safe and low42 suffixes. The result is a single
    full-tape blank-root certificate through Junc(0,0,136). -/
theorem blank_root_no_fatal_to_junc136 :
    ∃ d : Config,
      BB6Coverage.run target429 13718 blank = some d ∧
      Represents rootLow42End d ∧
      (∀ t : Nat, t ≤ 13718 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  obtain ⟨c0, hroot, hrep0, hprefix0⟩ := root_prefix_no_fatal_physical
  have hrepStart : Represents rootOuterStart c0 := by
    simpa [rootOuterStart, rootEndpoint, junc] using hrep0
  obtain ⟨d, htotal0, hrepEnd, houter, hlow⟩ :=
    blank_root_outer_low42_no_fatal 9243 c0 hroot hrepStart
  have hboundary : 9243 + rootOuterTime = 12641 := by
    rw [rootOuterTime_eq_3398]
  have htotalTime : 9243 + rootOuterTime + 1077 = 13718 := by
    rw [rootOuterTime_eq_3398]
  have htotal : BB6Coverage.run target429 13718 blank = some d := by
    simpa [htotalTime] using htotal0
  refine ⟨d, htotal, hrepEnd, ?_⟩
  intro t ht
  by_cases hfirst : t ≤ 9243
  · exact hprefix0 t hfirst
  · by_cases hsecond : t ≤ 12641
    · let s : Nat := t - 9243
      have hs : s ≤ rootOuterTime := by dsimp [s]; omega
      obtain ⟨e, he, hsafe⟩ := houter s hs
      have htime : t = 9243+s := by dsimp [s]; omega
      have hrun : BB6Coverage.run target429 t blank = some e := by
        simpa [htime] using he
      refine ⟨e, hrun, ?_⟩
      intro hbad
      exact hsafe ⟨hbad.1, hbad.2.1⟩
    · let s : Nat := t - 12641
      have hs : s ≤ 1077 := by dsimp [s]; omega
      obtain ⟨e, he, hsafe⟩ := hlow s hs
      have htime : t = 12641+s := by dsimp [s]; omega
      have hrun : BB6Coverage.run target429 t blank = some e := by
        rw [hboundary] at he
        simpa [htime] using he
      exact ⟨e, hrun, hsafe⟩

#print axioms blank_root_no_fatal_to_junc136

end BB429RootNoFatalChain
