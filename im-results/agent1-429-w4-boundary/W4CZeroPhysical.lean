import W4CZeroOrdinary
import W4CZeroSafe
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429W4CZeroPhysical

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429JuncHeadExcursion BB429W4CZeroSafe BB429W4CZeroOrdinary

/-- Generic physical bridge for a certified C/0-free zipper segment,
    including every primitive prefix and the endpoint. The conclusion
    holds on the literal source target429 bi-infinite tape, from any
    raw configuration representing the exact complete input zipper. -/
theorem physical_safe_all_prefix (n t : Nat) (z z' : Zipper)
    (c : Config) (hrep : Represents z c)
    (hsafe : runSafe n z = some z')
    (hend : (z'.state == 2 && !z'.current) = false)
    (ht : t ≤ n) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      (c'.state.val == 2 && !(c'.tape c'.head)) = false := by
  have hprefix : ∃ p, BB429OddExcursion.run t z = some p ∧
        (p.state == 2 && !p.current) = false := by
    by_cases hlt : t < n
    · exact runSafe_no_czero_prefix n t z z' hsafe hlt
    · have heq : t = n := by omega
      subst t
      exact ⟨z', runSafe_to_run n z z' hsafe, hend⟩
  obtain ⟨p, hsource, hno⟩ := hprefix
  obtain ⟨c', hraw, hrep'⟩ :=
    BB429PhysicalBridge.source_run_rep t z c hrep p hsource
  rcases hrep' with ⟨hstate, hcurrent, _, _⟩
  refine ⟨c', hraw, ?_⟩
  simpa only [hstate, hcurrent] using hno

/-- Every primitive prefix of every source E/1 crossing, from an
    arbitrarily positioned raw representation, avoids scanning C/0. -/
theorem physical_scanE_no_czero_all_prefix (b t : Nat)
    (suffix : List Bool) (c : Config)
    (hrep : Represents (sourceScanE b suffix) c)
    (ht : t ≤ crossTime b+1) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      (c'.state.val == 2 && !(c'.tape c'.head)) = false := by
  apply physical_safe_all_prefix (crossTime b+1) t
    (sourceScanE b suffix) (z 2 (finalLeft b) true suffix)
    c hrep (scanE_safe b suffix)
  · rfl
  · exact ht

/-- Exact physical C/0 exclusion for any ordinary positive-left
    Junc(u+1,v,w) transition, w>=2. -/
theorem physical_juncPos_no_czero_all_prefix (u v w t : Nat)
    (hw : 2 ≤ w) (c : Config)
    (hrep : Represents (junc (u+1) v w) c)
    (ht : t ≤ 4*v+10) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      (c'.state.val == 2 && !(c'.tape c'.head)) = false := by
  apply physical_safe_all_prefix (4*v+10) t
    (junc (u+1) v w) (junc u (v+2) (w-2)) c hrep
    (juncPos_next_safe u v w hw)
  · rfl
  · exact ht

/-- Exact physical C/0 exclusion for every ordinary zero-left
    Junc(0,v,w) transition, w>=3. -/
theorem physical_junc0_no_czero_all_prefix (v w t : Nat)
    (hw : 3 ≤ w) (c : Config)
    (hrep : Represents (junc 0 v w) c)
    (ht : t ≤ 2*v+27) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      (c'.state.val == 2 && !(c'.tape c'.head)) = false := by
  apply physical_safe_all_prefix (2*v+27) t
    (junc 0 v w) (junc (v+3) 0 (w-3)) c hrep
    (junc0_next_safe v w hw)
  · rfl
  · exact ht

/-- The same complete physical C/0-exclusion holds for an arbitrary
    finite batch of positive-left Junc transitions, all N and v. -/
theorem physical_juncPos_iter_no_czero_all_prefix
    (N U v w t : Nat) (hU : N ≤ U) (hw : 2*N ≤ w)
    (c : Config) (hrep : Represents (junc U v w) c)
    (ht : t ≤ juncPosFullTime N v) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      (c'.state.val == 2 && !(c'.tape c'.head)) = false := by
  apply physical_safe_all_prefix (juncPosFullTime N v) t
    (junc U v w) (junc (U-N) (v+2*N) (w-2*N)) c hrep
    (juncPos_iter_safe N U v w hU hw)
  · rfl
  · exact ht

#print axioms physical_safe_all_prefix
#print axioms physical_scanE_no_czero_all_prefix
#print axioms physical_juncPos_no_czero_all_prefix
#print axioms physical_junc0_no_czero_all_prefix
#print axioms physical_juncPos_iter_no_czero_all_prefix

end BB429W4CZeroPhysical
