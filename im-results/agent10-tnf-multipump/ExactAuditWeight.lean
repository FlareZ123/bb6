import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10ExactAuditWeight
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

/-- Re-evaluate only the exact sparse blank-delay weights. This traversal
does not run a machine, validate a FAR automaton, or replay a sweep. -/
def weightCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => weightOK p s n B
  | .cycle .. => true
  | .far .. => true
  | .proven .. => true
  | .split n s kids => weightOK p s n B &&
      allMoves (fun mv => weightCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem reweight_query {B C : Nat} {p : PartialMachine} {n : Nat} {s : Slot}
    (h : zipQueryOK B p n s = true) (hw : weightOK p s n C = true) :
    zipQueryOK C p n s = true := by
  simp only [zipQueryOK, Bool.and_eq_true] at h ⊢
  exact ⟨h.1,h.2.1,hw⟩

theorem reweight {B C : Nat} (p : PartialMachine) (t : Audit)
    (h : zipCheck B p t = true) (hw : weightCheck C p t = true) :
    zipCheck C p t = true := by
  induction t generalizing p with
  | last n s =>
    simp only [zipCheck,Bool.and_eq_true] at h ⊢
    exact ⟨reweight_query h.1 (by simpa only [weightCheck] using hw),h.2⟩
  | cycle e k r b => exact h
  | far rev d cert => exact h
  | proven q safe => exact h
  | split n s kids ih =>
    simp only [zipCheck,Bool.and_eq_true] at h ⊢
    simp only [weightCheck,Bool.and_eq_true] at hw
    refine ⟨reweight_query h.1 hw.1, allMoves_of _ ?_⟩
    intro mv
    exact ih mv (refine p s (some mv))
      (allMoves_sound _ h.2 mv) (allMoves_sound _ hw.2 mv)

/-- A real first query to a hole gives a halting completion for every
possible incoming delay of the halt refinement. Thus this weight test
is necessary as well as sufficient, irrespective of other descendants. -/
theorem query_weight_necessary {B C : Nat} {p : PartialMachine} {n : Nat} {s : Slot}
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hq : zipQueryOK B p n s = true)
    (hbound : ∀ m, compatible p m → WeightedBound C m) :
    weightOK p s n C = true := by
  obtain ⟨hread,hhole,_⟩ := zipQueryOK_sound hq
  have hfirst := refine_preserves_firstOne p s none hhole hroot
  have hh : ∀ m, compatible (refine p s none) m → HaltsAfter m n := by
    intro m hm
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      exact first_hole_halts p n c hr
        (by simpa only [hs] using hhole) m (by simpa only [hs] using hm)
  have hc : ∀ m, compatible (refine p s none) m → WeightedBound C m :=
    fun m hm => hbound m (refine_preserves_compat p m s none hhole hm)
  have hd := (uniform_halter_weight_iff (refine p s none) C n hfirst hh).mp hc
  unfold weightOK
  apply List.all_eq_true.mpr
  intro d h
  exact decide_eq_true (hd d h)

theorem weight_necessary {B C : Nat} (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (h : zipCheck B p t = true)
    (hbound : ∀ m, compatible p m → WeightedBound C m) :
    weightCheck C p t = true := by
  induction t generalizing p with
  | last n s =>
    simp only [zipCheck,Bool.and_eq_true] at h
    exact query_weight_necessary hroot h.1 hbound
  | cycle e k r b => rfl
  | far rev d cert => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    simp only [zipCheck,Bool.and_eq_true] at h
    simp only [weightCheck,Bool.and_eq_true]
    have hhole := (zipQueryOK_sound h.1).2.1
    refine ⟨query_weight_necessary hroot h.1 hbound,allMoves_of _ ?_⟩
    intro mv
    exact ih mv (refine p s (some mv))
      (refine_preserves_firstOne p s (some mv) hhole hroot)
      (allMoves_sound _ h.2 mv)
      (fun m hm => hbound m (refine_preserves_compat p m s (some mv) hhole hm))

/-- An accepted audit tree determines the exact weighted threshold,
without any further transition replay. -/
theorem exact_weight_iff {B C : Nat} (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : zipCheck B p t = true) :
    (∀ m, compatible p m → WeightedBound C m) ↔ weightCheck C p t = true := by
  constructor
  · exact weight_necessary p t hroot h
  · intro hw
    exact (certifiedZip C p t hroot hno (reweight p t h hw)).sound

#print axioms reweight
#print axioms exact_weight_iff
end BB6.Agent10ExactAuditWeight
