import ZipWeightTighten

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4ZipWeightTighten
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

/-- Every accepted query admits a halting completion. All its graph delays
    are realizable, hence every uniform bound must pay its full weight. -/
theorem queryWeight_complete {A B p n s}
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (old : zipQueryOK A p n s = true)
    (hbound : ∀ m, compatible p m → WeightedBound B m) :
    queryWeight B p n s = true := by
  obtain ⟨hr,hh,_⟩ := zipQueryOK_sound old
  have hroot' := refine_preserves_firstOne p s none hh hroot
  have hhalt : ∀ m, compatible (refine p s none) m → HaltsAfter m n := by
    intro m hm
    cases hrun : knownRun p n with
    | none => simp [hrun] at hr
    | some c =>
      have hs : readSlot c = s := by simpa [hrun] using hr
      exact first_hole_halts p n c hrun (by simpa [hs] using hh) m (by simpa [hs] using hm)
  have hbound' : ∀ m, compatible (refine p s none) m → WeightedBound B m := by
    intro m hm
    exact hbound m (refine_preserves_compat p m s none hh hm)
  have hd := (uniform_halter_weight_iff (refine p s none) B n hroot' hhalt).mp hbound'
  have hw : weightOK p s n B = true := by
    unfold weightOK
    apply List.all_eq_true.mpr
    intro d hmem
    exact decide_eq_true (hd d hmem)
  simp [queryWeight,hw]

/-- Every uniform weighted bound on a certified tree satisfies every query
    weight. The proof uses attainable halting completions, not a converse
    assumption about a nonhalting certificate. -/
theorem weights_complete (A B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (old : zipCheck A p t = true)
    (hbound : ∀ m, compatible p m → WeightedBound B m) :
    weights B p t = true := by
  induction t generalizing p with
  | last n s =>
    simp only [zipCheck, Bool.and_eq_true] at old
    exact queryWeight_complete hroot old.1 hbound
  | cycle e k r b => rfl
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    simp only [zipCheck, Bool.and_eq_true] at old
    simp only [weights, Bool.and_eq_true]
    obtain ⟨_,hh,_⟩ := zipQueryOK_sound old.1
    refine ⟨queryWeight_complete hroot old.1 hbound, allMoves_of _ ?_⟩
    intro mv
    exact ih mv (refine p s (some mv))
      (refine_preserves_firstOne p s (some mv) hh hroot)
      (allMoves_sound _ old.2 mv)
      (fun m hm => hbound m (refine_preserves_compat p m s (some mv) hh hm))

/-- Exact decision procedure for the uniform weighted bound of any accepted
    Audit tree with the standard first-one root and no assigned halt. -/
theorem weights_exact (A B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (old : zipCheck A p t = true) :
    (∀ m, compatible p m → WeightedBound B m) ↔ weights B p t = true := by
  constructor
  · exact weights_complete A B p t hroot old
  · intro hw
    exact (certifiedZip B p t hroot hno (transfer A B p t old hw)).sound

#print axioms queryWeight_complete
#print axioms weights_complete
#print axioms weights_exact
end BB6.Agent4ZipWeightTighten
