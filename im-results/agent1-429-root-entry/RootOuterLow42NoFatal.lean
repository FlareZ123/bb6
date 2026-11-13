import OuterSafe
import Low42RootNoFatal
import BB429PhysicalBridge
import BB429FinishScanEDelta
import BubbleExact
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 30000000

namespace BB429RootOuterLow42NoFatal

open BB6Coverage BB6Bubble BB429PhysicalFrontier
open BB429OddExcursion BB429FinishScanEDelta
open BB429PhysicalBridge BB429W4CZeroSafe
open BB429PhysicalGuardSafe BB429OuterSafe
open BB429Low42RootNoFatal

def rootOuterStart : Zipper := junc 11 0 98
def rootOuterMiddle : Zipper := junc 25 0 73
def rootOuterEnd : Zipper := junc 53 0 20

/-- The two certified outer returns from J(11,98) to J(53,20). -/
def rootOuterTime : Nat := outerCost 11 0 + outerCost 25 0

theorem rootOuterTime_eq_3398 : rootOuterTime = 3398 := by
  decide

theorem rootOuterTime_plus_low42_eq_4475 :
    rootOuterTime + 1077 = 4475 := by
  decide

/-- The entire two-branch high-three suffix is C/0-free in the original
    source semantics, for all 3398 primitive steps. -/
theorem root_outer_safe_source :
    runSafe rootOuterTime rootOuterStart = some rootOuterEnd := by
  have h1 : runSafe (outerCost 11 0) rootOuterStart =
      some rootOuterMiddle := by
    simpa [rootOuterStart, rootOuterMiddle] using
      junc_outer_safe 11 0 98 (by omega)
  have h2 : runSafe (outerCost 25 0) rootOuterMiddle =
      some rootOuterEnd := by
    simpa [rootOuterMiddle, rootOuterEnd] using
      junc_outer_safe 25 0 73 (by omega)
  unfold rootOuterTime
  rw [runSafe_add, h1]
  simpa using h2

/-- Physical all-prefix lift of the two outer returns. This is stronger
    than merely excluding the fatal C/01 gate: no C/0 configuration occurs
    anywhere in the 3398-step suffix, including its endpoint. -/
theorem root_outer_no_czero_physical
    (c : Config) (hrep : Represents rootOuterStart c) :
    ∃ d : Config,
      BB6Coverage.run target429 rootOuterTime c = some d ∧
      Represents rootOuterEnd d ∧
      (∀ t : Nat, t ≤ rootOuterTime →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false)) := by
  have hsource :
      BB429OddExcursion.run rootOuterTime rootOuterStart =
        some rootOuterEnd :=
    runSafe_to_run rootOuterTime rootOuterStart rootOuterEnd
      root_outer_safe_source
  obtain ⟨d, hraw, hrepD⟩ :=
    source_run_rep rootOuterTime rootOuterStart c hrep rootOuterEnd hsource
  refine ⟨d, hraw, hrepD, ?_⟩
  intro t ht
  by_cases hlt : t < rootOuterTime
  · exact physical_guarded_prefix rootOuterTime t
      rootOuterStart rootOuterEnd c hrep root_outer_safe_source hlt
  · have hteq : t = rootOuterTime := by omega
    subst t
    refine ⟨d, hraw, ?_⟩
    intro hbad
    have hs : d.state.val = rootOuterEnd.state := hrepD.1
    have hs0 : rootOuterEnd.state = 0 := by rfl
    rw [hs0] at hs
    omega

private theorem physical_run_add (m n : Nat) (a b c : Config)
    (h1 : BB6Coverage.run target429 m a = some b)
    (h2 : BB6Coverage.run target429 n b = some c) :
    BB6Coverage.run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add', h1]
  exact h2

/-- Blank-root composition of the physical outer no-C/0 certificate. -/
theorem blank_root_outer_no_czero
    (n : Nat) (c : Config)
    (hentry : BB6Coverage.run target429 n blank = some c)
    (hrep : Represents rootOuterStart c) :
    ∃ d : Config,
      BB6Coverage.run target429 (n + rootOuterTime) blank = some d ∧
      Represents rootOuterEnd d ∧
      (∀ t : Nat, t ≤ rootOuterTime →
        ∃ e : Config,
          BB6Coverage.run target429 (n+t) blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false)) := by
  obtain ⟨d, hraw, hrepD, hprefix⟩ :=
    root_outer_no_czero_physical c hrep
  refine ⟨d, ?_, hrepD, ?_⟩
  · exact physical_run_add n rootOuterTime blank c d hentry hraw
  · intro t ht
    obtain ⟨e, he, hgood⟩ := hprefix t ht
    refine ⟨e, ?_, hgood⟩
    exact physical_run_add n t blank c e hentry he

/-- An authentic blank-root entry into Junc(11,0,98) has a completely
    certified 4475-step continuation to Junc(0,0,136). The first 3398
    steps contain no C/0 at all; the final 1077 steps have exactly the
    two blank-right C/0 visits certified in Low42RootNoFatal. -/
theorem blank_root_outer_low42_no_fatal
    (n : Nat) (c : Config)
    (hentry : BB6Coverage.run target429 n blank = some c)
    (hrep : Represents rootOuterStart c) :
    ∃ d : Config,
      BB6Coverage.run target429 (n + rootOuterTime + 1077) blank = some d ∧
      Represents rootLow42End d ∧
      (∀ t : Nat, t ≤ rootOuterTime →
        ∃ e : Config,
          BB6Coverage.run target429 (n+t) blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false)) ∧
      (∀ t : Nat, t ≤ 1077 →
        ∃ e : Config,
          BB6Coverage.run target429 (n + rootOuterTime + t) blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  obtain ⟨c1, hentry1, hrep1, hprefix1⟩ :=
    blank_root_outer_no_czero n c hentry hrep
  obtain ⟨d, hentry2, hrep2, hprefix2⟩ :=
    blank_root_low42_no_fatal (n+rootOuterTime) c1 hentry1 hrep1
  exact ⟨d, hentry2, hrep2, hprefix1, hprefix2⟩

#print axioms rootOuterTime_eq_3398
#print axioms rootOuterTime_plus_low42_eq_4475
#print axioms root_outer_safe_source
#print axioms root_outer_no_czero_physical
#print axioms blank_root_outer_no_czero
#print axioms blank_root_outer_low42_no_fatal

end BB429RootOuterLow42NoFatal
