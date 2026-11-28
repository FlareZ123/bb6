import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12Raw46
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

def route : List PathEntry := (path.take 3) ++ [(5,(3,true),⟨false,false,2⟩)]
abbrev parent : PartialMachine := (pathEnd root 2 route).1
abbrev child (mv : Move) : PartialMachine := refine parent (2,true) (some mv)
theorem parent_path : FirstHolePath parent 4 := pathOK_sound root 2 route FirstHolePath.root (by decide)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  pathEnd_nohalt root 2 route firstOneCylinder_no_assigned_halt
theorem parent_support : TNFSupport parent 4 := by
  have h0 := firstOneCylinder_tnf_support
  have h1 := refine_support root (1,false) ⟨true,true,2⟩ 2 3 h0 (by decide) (by decide) (by decide)
  have h2 := refine_support _ (2,false) ⟨false,true,3⟩ 3 4 h1 (by decide) (by decide) (by decide)
  have h3 := refine_support _ (3,false) ⟨true,false,3⟩ 4 4 h2 (by decide) (by decide) (by decide)
  exact refine_support _ (3,true) ⟨false,false,2⟩ 4 4 h3 (by decide) (by decide) (by decide)

theorem firstQuery : (knownRun parent 6).map readSlot = some (2,true) := by decide

theorem cycle0LA : ∀ m, compatible (child ⟨false,false,0⟩) m → NeverHalts m :=
  zipCycle_sound _ 2 9 false (3) (by decide) (by decide)

theorem cycle0LB : ∀ m, compatible (child ⟨false,false,1⟩) m → NeverHalts m :=
  zipCycle_sound _ 13 1 false (-1) (by decide) (by decide)

theorem cycle0LC : ∀ m, compatible (child ⟨false,false,2⟩) m → NeverHalts m :=
  zipCycle_sound _ 8 1 false (0) (by decide) (by decide)

theorem cycle0LD : ∀ m, compatible (child ⟨false,false,3⟩) m → NeverHalts m :=
  zipCycle_sound _ 7 1 false (-1) (by decide) (by decide)

theorem cycle0RC : ∀ m, compatible (child ⟨false,true,2⟩) m → NeverHalts m :=
  zipCycle_sound _ 10 1 false (2) (by decide) (by decide)

theorem cycle0RD : ∀ m, compatible (child ⟨false,true,3⟩) m → NeverHalts m :=
  zipCycle_sound _ 7 1 false (1) (by decide) (by decide)

theorem cycle1LC : ∀ m, compatible (child ⟨true,false,2⟩) m → NeverHalts m :=
  zipCycle_sound _ 10 1 false (0) (by decide) (by decide)

theorem cycle1LD : ∀ m, compatible (child ⟨true,false,3⟩) m → NeverHalts m :=
  zipCycle_sound _ 7 1 false (-1) (by decide) (by decide)

theorem cycle1RC : ∀ m, compatible (child ⟨true,true,2⟩) m → NeverHalts m :=
  zipCycle_sound _ 14 1 false (0) (by decide) (by decide)

theorem cycle1RD : ∀ m, compatible (child ⟨true,true,3⟩) m → NeverHalts m :=
  zipCycle_sound _ 10 1 false (0) (by decide) (by decide)

def unresolved : List Move := [⟨false,false,4⟩,⟨false,true,0⟩,⟨false,true,1⟩,⟨false,true,4⟩,⟨true,false,0⟩,⟨true,false,1⟩,⟨true,false,4⟩,⟨true,true,0⟩,⟨true,true,1⟩,⟨true,true,4⟩]

/-- Conditional Raw46 assembly. Only these ten canonical ordinary children
remain premises; the halt and all translated-cycle children are closed. -/
theorem weighted_of_children (h : ∀ mv ∈ unresolved, ∀ m, compatible (child mv) m → WeightedBound 7014 m) :
    ∀ m, compatible parent m → WeightedBound 7014 m := by
  have halt : ∀ m, compatible (refine parent (2,true) none) m → WeightedBound 7014 m := by
    have H := firstQuery
    cases hr : knownRun parent 6 with
    | none => simp [hr] at H
    | some c =>
      have hs : readSlot c = (2,true) := by simpa [hr] using H
      have hh : parent (readSlot c) = none := by rw [hs]; decide
      have hw : ∀ d ∈ possibleDelays (refine parent (readSlot c) none) 0, d+6+1 ≤ 7014 := by
        rw [hs]
        exact weightOK_sound _ _ _ _ (by decide)
      simpa only [hs] using first_hole_weighted_halt 7014 parent 6 c parent_root hr hh hw
  apply tnf_branch_sound 7014 4 parent (2,true) (by decide) parent_support (by decide) (by decide) parent_root halt
  · intro mv hlt
    rcases mv with ⟨w,r,q⟩
    change q.val < 4 at hlt
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases hq with rfl|rfl|rfl|rfl <;> cases w <;> cases r
    · intro m hm; exact weighted_never 7014 m (cycle0LA m hm)
    · exact h _ (by decide)
    · exact h _ (by decide)
    · exact h _ (by decide)
    · intro m hm; exact weighted_never 7014 m (cycle0LB m hm)
    · exact h _ (by decide)
    · exact h _ (by decide)
    · exact h _ (by decide)
    · intro m hm; exact weighted_never 7014 m (cycle0LC m hm)
    · intro m hm; exact weighted_never 7014 m (cycle0RC m hm)
    · intro m hm; exact weighted_never 7014 m (cycle1LC m hm)
    · intro m hm; exact weighted_never 7014 m (cycle1RC m hm)
    · intro m hm; exact weighted_never 7014 m (cycle0LD m hm)
    · intro m hm; exact weighted_never 7014 m (cycle0RD m hm)
    · intro m hm; exact weighted_never 7014 m (cycle1LD m hm)
    · intro m hm; exact weighted_never 7014 m (cycle1RD m hm)
  · intro q hq w r
    have H : q = 4 := by omega
    subst q
    cases w <;> cases r <;> exact h _ (by decide)

theorem cover_of_children (h : ∀ mv ∈ unresolved, Cover (WeightedBound 7014) (child mv)) :
    Cover (WeightedBound 7014) parent :=
  .leaf parent (weighted_of_children (fun mv hm => (h mv hm).sound))
#print axioms parent_path
#print axioms weighted_of_children
#print axioms cover_of_children
end BB6.Agent12Raw46
