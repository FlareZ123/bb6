import PackedAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent3OneLBParent
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper BB6.Agent3PackedAudit
open BB6.Agent31ThreeHole BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath
open BB6.Agent3PackedCycle

def B : Nat := 187672026
def parent : PartialMachine := fromCodes [7,24,11,24,14,24,24,16,6,11,24,24]
def slot : Slot := (2,true)
def child (i : Nat) : PartialMachine := fromCodes [7,24,11,24,14,i,24,16,6,11,24,24]
def cycleCodes : List Nat := [11,12,14,16,17,18]
def openCodes : List Nat := [0,1,2,3,4,5,6,7,8,9,10,13,15,19,20,21,22,23]

theorem firstQuery : packedQueryOK B parent 9 slot = true := by decide +kernel
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel

theorem haltChild : Cover (WeightedBound B) (refine parent slot none) := by
  obtain ⟨hr,hu,hw⟩ := packedQueryOK_sound firstQuery
  cases h : knownRun parent 9 with
  | none => simp [h] at hr
  | some c =>
    have hs : readSlot c = slot := by simpa [h] using hr
    apply Cover.leaf
    intro m hm
    exact first_hole_weighted_halt B parent 9 c root h
      (by simpa [hs] using hu)
      (by simpa [hs] using weightOK_sound parent slot 9 B hw) m
      (by simpa [hs] using hm)

theorem ordinaryExact (mv : Move) :
    ∃ i ∈ List.range 24, refine parent slot (some mv) = child i := by
  have h : allMoves (fun v => (List.range 24).any
    (fun i => tableOK (refine parent slot (some v)) (child i))) = true := by decide +kernel
  obtain ⟨i,hi,he⟩ := List.any_eq_true.mp (allMoves_sound _ h mv)
  exact ⟨i,hi,tableOK_sound _ _ he⟩

theorem openComplete (i : Nat) (hi : i ∈ List.range 24) (hn : i ∉ cycleCodes) :
    i ∈ openCodes := by
  have h : (List.range 24).all (fun i => decide (i ∈ cycleCodes ∨ i ∈ openCodes)) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp h i hi)).resolve_left hn

theorem cycleCover (i : Nat) (hi : i ∈ cycleCodes) : Cover (WeightedBound B) (child i) := by
  simp only [cycleCodes,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Cover.leaf _ (fun m hm => weighted_never B m
      (cycleH_sound (child 11) 2 8 false (2) (by decide) (by decide +kernel) m hm))
  · exact Cover.leaf _ (fun m hm => weighted_never B m
      (cycleH_sound (child 12) 6 4 false (0) (by decide) (by decide +kernel) m hm))
  · exact Cover.leaf _ (fun m hm => weighted_never B m
      (cycleH_sound (child 14) 6 4 false (0) (by decide) (by decide +kernel) m hm))
  · exact Cover.leaf _ (fun m hm => weighted_never B m
      (cycleH_sound (child 16) 4 6 false (1) (by decide) (by decide +kernel) m hm))
  · exact Cover.leaf _ (fun m hm => weighted_never B m
      (cycleH_sound (child 17) 14 3 true (2) (by decide) (by decide +kernel) m hm))
  · exact Cover.leaf _ (fun m hm => weighted_never B m
      (cycleH_sound (child 18) 9 2 true (-2) (by decide) (by decide +kernel) m hm))

/-- Exactly all 25 C1 choices, including the genuine halt and six local cycles.
    The remaining 18 independently bounded producers are explicit premises. -/
theorem parent_cover_of (kids : ∀ i ∈ openCodes, Cover (WeightedBound B) (child i)) :
    Cover (WeightedBound B) parent := by
  apply Cover.branch parent slot (by decide +kernel)
  intro t _
  cases t with
  | none => exact haltChild
  | some mv =>
    obtain ⟨i,hi,he⟩ := ordinaryExact mv
    rw [he]
    by_cases hc : i ∈ cycleCodes
    · exact cycleCover i hc
    · exact kids i (openComplete i hi hc)

#print axioms parent_cover_of
end BB6.Agent3OneLBParent
