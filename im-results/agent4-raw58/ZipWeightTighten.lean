import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4ZipWeightTighten
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

/-- A cheap query-weight check. The universal five-step delay cap makes
    graph enumeration unnecessary except at queries near the target. -/
def queryWeight (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (n + 6 ≤ B) || weightOK p s n B

theorem queryWeight_sound {B p n s} (h : queryWeight B p n s = true) :
    weightOK p s n B = true := by
  simp only [queryWeight, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · unfold weightOK
    apply List.all_eq_true.mpr
    intro d hd
    unfold possibleDelays at hd
    have hlt := List.mem_range.mp (List.mem_filter.mp hd).1
    exact decide_eq_true (by omega)
  · exact h

/-- Only weights are inspected. Previously accepted run, cycle, FAR and
    imported semantic certificates are not evaluated again. -/
def weights (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => queryWeight B p n s
  | .split n s kids => queryWeight B p n s &&
      allMoves (fun mv => weights B (refine p s (some mv)) (kids mv))
  | _ => true
termination_by structural t => t

theorem query_transfer {A B p n s} (old : zipQueryOK A p n s = true)
    (hw : queryWeight B p n s = true) : zipQueryOK B p n s = true := by
  simp only [zipQueryOK, Bool.and_eq_true] at old ⊢
  exact ⟨old.1, old.2.1, queryWeight_sound hw⟩

/-- The full accepted Audit at any old bound transfers to a new bound if
    its independent weight requirements are certified. No replay occurs. -/
theorem transfer (A B : Nat) (p : PartialMachine) (t : Audit)
    (old : zipCheck A p t = true) (hw : weights B p t = true) :
    zipCheck B p t = true := by
  induction t generalizing p with
  | last n s =>
    simp only [zipCheck, Bool.and_eq_true] at old ⊢
    exact ⟨query_transfer old.1 hw, old.2⟩
  | cycle e k r b => exact old
  | far rev d C => exact old
  | proven q safe => exact old
  | split n s kids ih =>
    simp only [zipCheck, Bool.and_eq_true] at old ⊢
    simp only [weights, Bool.and_eq_true] at hw
    exact ⟨query_transfer old.1 hw.1, allMoves_of _ (fun mv =>
      ih mv (refine p s (some mv)) (allMoves_sound _ old.2 mv)
        (allMoves_sound _ hw.2 mv))⟩

#print axioms queryWeight_sound
#print axioms query_transfer
#print axioms transfer
end BB6.Agent4ZipWeightTighten
