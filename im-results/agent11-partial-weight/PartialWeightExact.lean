import AuditReweight
import ZipWeightExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Necessary *and* sufficient weight-only tests for previously certified
partial-Audit trees, under explicit Covers for every unresolved residual.

The forward direction does not assume residual coverage: any actual uniform
bound necessarily pays every reachable query's exact blank-delay surcharge.
The reverse direction uses the independently proved partialSound theorem
and retains all residual hypotheses. This generalizes ZipWeightExact from
closed audit trees to the unresolved-frontier representation used by Raw112.
-/

namespace BB6.Agent11PartialWeightExact

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent50TNFPilot BB6.Agent10ZipAudit
open BB6.Agent47PartialAudit BB6.Agent32AuditReweight

theorem quick_weight_necessary {A B : Nat} {p : PartialMachine} {n : Nat}
    {s : Slot}
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (old : zipQueryOK A p n s = true)
    (hbound : ∀ m, compatible p m → WeightedBound B m) :
    quickWeight B p n s = true := by
  have h := BB6.Agent4ZipWeightTighten.queryWeight_complete hroot old hbound
  unfold BB6.Agent4ZipWeightTighten.queryWeight at h
  unfold quickWeight
  by_cases hn : n + 6 ≤ B
  · simp [hn]
  · simpa [hn] using h

theorem weight_audit_necessary (A B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (old : zipCheck A p t = true)
    (hbound : ∀ m, compatible p m → WeightedBound B m) :
    weightAudit B p t = true := by
  induction t generalizing p with
  | last n s =>
    simp only [zipCheck, Bool.and_eq_true] at old
    exact quick_weight_necessary hroot old.1 hbound
  | cycle e k r b => exact rfl
  | far rev d C => exact rfl
  | proven q safe => exact rfl
  | split n s kids ih =>
    simp only [zipCheck, Bool.and_eq_true] at old
    simp only [weightAudit, Bool.and_eq_true]
    obtain ⟨_,hh,_⟩ := zipQueryOK_sound old.1
    refine ⟨quick_weight_necessary hroot old.1 hbound, allMoves_of _ ?_⟩
    intro mv
    exact ih mv (refine p s (some mv))
      (refine_preserves_firstOne p s (some mv) hh hroot)
      (allMoves_sound _ old.2 mv)
      (fun m hm => hbound m (refine_preserves_compat p m s (some mv) hh hm))

theorem partial_weights_necessary (A B : Nat) (p : PartialMachine)
    (t : PartialAudit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (old : partialCheck A p t = true)
    (hbound : ∀ m, compatible p m → WeightedBound B m) :
    partialWeights B p t = true := by
  induction t generalizing p with
  | unresolved => rfl
  | closed t => exact weight_audit_necessary A B p t hroot old hbound
  | split n s kids ih =>
    simp only [partialCheck, Bool.and_eq_true] at old
    simp only [partialWeights, Bool.and_eq_true]
    obtain ⟨_,hh,_⟩ := zipQueryOK_sound old.1
    refine ⟨quick_weight_necessary hroot old.1 hbound, allMoves_of _ ?_⟩
    intro mv
    exact ih mv (refine p s (some mv))
      (refine_preserves_firstOne p s (some mv) hh hroot)
      (allMoves_sound _ old.2 mv)
      (fun m hm => hbound m (refine_preserves_compat p m s (some mv) hh hm))

/-- Exact B-bound criterion after every unresolved residual has its own B-bound.
    No query trace is rerun, and no unresolved leaf is discarded. -/
theorem partial_weights_exact (A B : Nat) (p : PartialMachine)
    (t : PartialAudit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (old : partialCheck A p t = true)
    (hres : ∀ e ∈ partialResiduals p t,
      ∀ m, compatible e.2 m → WeightedBound B m) :
    (∀ m, compatible p m → WeightedBound B m) ↔
      partialWeights B p t = true := by
  constructor
  · exact partial_weights_necessary A B p t hroot old
  · intro hw m hm
    have hnew := partial_reweight A B p t old hw
    rcases partialSound B p t hroot hno hnew m hm with hb | ⟨e,he,hc⟩
    · exact hb
    · exact hres e he m hc

#print axioms quick_weight_necessary
#print axioms weight_audit_necessary
#print axioms partial_weights_necessary
#print axioms partial_weights_exact

end BB6.Agent11PartialWeightExact
