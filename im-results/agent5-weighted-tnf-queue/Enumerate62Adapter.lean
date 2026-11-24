import WeightedTNFCertificate

namespace BB6.Agent5Enumerate62
open BB6Coverage
open BB6.Agent13BlankDelay

/--
Faithful finite-state encoding of the pinned Enumerate62.v TNF node table.
Coq's A..F are Fin 6 in that order, S0/S1 are false/true, and L/R are
false/true. In a TNF node, a missing Coq transition is an unexpanded slot;
the local PartialMachine therefore stores it as outer none, not as an
assigned halting transition.
-/
abbrev SourceTM := Slot → Option Move

def sourcePartial (tm : SourceTM) : PartialMachine :=
  fun s => (tm s).map (fun mv => some mv)

def sourceHoles (tm : SourceTM) : Finset Slot :=
  Finset.univ.filter (fun s => tm s = none)

def sourceUndefCount (tm : SourceTM) : Nat :=
  (sourceHoles tm).card

def sourceSupport (tm : SourceTM) (cut : Nat) : Prop :=
  ∀ s mv, tm s = some mv →
    s.1.val < cut ∧ mv.next.val < cut

theorem sourceSupport_to_tnfSupport (tm : SourceTM) (cut : Nat)
    (hs : sourceSupport tm cut) :
    TNFSupport (sourcePartial tm) cut := by
  intro s t ht
  cases htm : tm s with
  | none =>
      simp [sourcePartial, htm] at ht
  | some mv =>
      have ht' : t = some mv := by
        simpa [sourcePartial, htm] using ht
      subst t
      exact ⟨(hs s mv htm).1, by
        intro v hv
        cases hv
        exact (hs s mv htm).2⟩

/-- The exact node0 table from Enumerate62.v:
    TM_from_str "1RB---_------_------_------_------_------". -/
def sourceRootTM : SourceTM :=
  fun s => if s = initialSlot then some ⟨true, true, (1 : Fin 6)⟩ else none

structure SourceNode where
  tm : SourceTM
  holes : Nat
  fresh : Nat

def sourceRoot : SourceNode := ⟨sourceRootTM, 11, 2⟩

theorem sourceRoot_action :
    sourcePartial sourceRootTM initialSlot =
      some (some ⟨true, true, (1 : Fin 6)⟩) := by
  simp [sourcePartial, sourceRootTM]

theorem sourceRoot_support : sourceSupport sourceRootTM 2 := by
  intro s mv h
  by_cases hs : s = initialSlot
  · subst s
    simp [sourceRootTM] at h
    cases h
    exact ⟨by decide, by decide⟩
  · simp [sourceRootTM, hs] at h

theorem sourceRoot_holes : sourceUndefCount sourceRootTM = 11 := by
  decide

def sourceUpdate (tm : SourceTM) (slot : Slot) (mv : Move) : SourceTM :=
  fun s => if s = slot then some mv else tm s

theorem sourceHoles_update (tm : SourceTM) (slot : Slot) (mv : Move)
    (hhole : tm slot = none) :
    sourceHoles (sourceUpdate tm slot mv) = (sourceHoles tm).erase slot := by
  ext s
  by_cases hs : s = slot
  · subst s
    simp [sourceHoles, sourceUpdate, hhole]
  · simp [sourceHoles, sourceUpdate, hs]

theorem sourceUndefCount_update (tm : SourceTM) (slot : Slot) (mv : Move)
    (hhole : tm slot = none) :
    sourceUndefCount (sourceUpdate tm slot mv) =
      sourceUndefCount tm - 1 := by
  unfold sourceUndefCount
  rw [sourceHoles_update tm slot mv hhole]
  have hmem : slot ∈ sourceHoles tm := by
    simp [sourceHoles, hhole]
  simp [Finset.card_erase_of_mem hmem]

/-- A single missing source transition is the unique hole when the
    source TNF count is one. This is the exact finite-table fact used by
    Enumerate62.v's expand' last-hole shortcut. -/
theorem source_last_hole_rest (tm : SourceTM) (slot : Slot)
    (hcount : sourceUndefCount tm = 1) (hhole : tm slot = none) :
    ∀ s, s ≠ slot → ∃ mv, tm s = some mv := by
  intro s hne
  by_contra hnot
  have hsnone : tm s = none := by
    cases ht : tm s with
    | none => rfl
    | some mv => simp [ht] at hnot
  have hslot : slot ∈ sourceHoles tm := by
    simp [sourceHoles, hhole]
  have hs : s ∈ sourceHoles tm := by
    simp [sourceHoles, hsnone]
  have hsubset : insert slot {s} ⊆ sourceHoles tm := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ht | ht
    · subst t
      exact hslot
    · subst t
      exact hs
  have hcard : (insert slot {s} : Finset Slot).card ≤ (sourceHoles tm).card :=
    Finset.card_le_card hsubset
  have htwo : (insert slot {s} : Finset Slot).card = 2 := by
    simp [hne]
  rw [htwo] at hcard
  omega

def sourceChildFresh (x : SourceNode) (mv : Move) : Nat :=
  if mv.next.val = x.fresh then x.fresh + 1 else x.fresh

def sourceChild (x : SourceNode) (slot : Slot) (mv : Move) : SourceNode :=
  { tm := sourceUpdate x.tm slot mv
    holes := x.holes - 1
    fresh := sourceChildFresh x mv }

theorem sourceChildFresh_ge (x : SourceNode) (mv : Move) :
    x.fresh ≤ sourceChildFresh x mv := by
  unfold sourceChildFresh
  split <;> omega

theorem sourceChildFresh_gt_dest (x : SourceNode) (mv : Move)
    (hdest : mv.next.val ≤ x.fresh) :
    mv.next.val < sourceChildFresh x mv := by
  unfold sourceChildFresh
  by_cases heq : mv.next.val = x.fresh <;> simp [heq] <;> omega

theorem sourceChild_partial (x : SourceNode) (slot : Slot) (mv : Move) :
    sourcePartial (sourceChild x slot mv).tm =
      refine (sourcePartial x.tm) slot (some mv) := by
  funext s
  by_cases hs : s = slot <;>
    simp [sourceChild, sourceUpdate, sourcePartial, refine, hs]

theorem sourceChild_support (x : SourceNode) (slot : Slot) (mv : Move)
    (hs : sourceSupport x.tm x.fresh)
    (hslot : slot.1.val < x.fresh)
    (hdest : mv.next.val ≤ x.fresh) :
    sourceSupport (sourceChild x slot mv).tm
      (sourceChild x slot mv).fresh := by
  intro s v hv
  by_cases he : s = slot
  · subst s
    have hv' : v = mv := by
      simp [sourceChild, sourceUpdate] at hv
      exact Option.some.inj hv
    subst v
    exact ⟨Nat.lt_of_lt_of_le hslot (sourceChildFresh_ge x mv),
      sourceChildFresh_gt_dest x mv hdest⟩
  · have htm : x.tm s = some v := by
      simpa [sourceChild, sourceUpdate, he] using hv
    obtain ⟨hsrc, hdst⟩ := hs s v htm
    have hle := sourceChildFresh_ge x mv
    exact ⟨Nat.lt_of_lt_of_le hsrc hle, Nat.lt_of_lt_of_le hdst hle⟩

/-- The source's nested loops enumerate four write/direction choices for
    every old label below cut, plus four choices for the least fresh label
    equal to cut. This filter is exactly that set: q.val ≤ cut. -/
def sourceChoices (cut : Nat) : List Move :=
  ((List.finRange 6).filter (fun q => q.val ≤ cut)).flatMap
    (fun q =>
      [⟨false, false, q⟩, ⟨false, true, q⟩,
       ⟨true, false, q⟩, ⟨true, true, q⟩])

theorem sourceChoices_mem_iff (cut : Nat) (mv : Move) :
    mv ∈ sourceChoices cut ↔ mv.next.val ≤ cut := by
  constructor
  · intro h
    obtain ⟨q, hq, hmv⟩ := List.mem_flatMap.mp h
    have hq' : q.val ≤ cut := (List.mem_filter.mp hq).2
    have heq : mv.next = q := by
      cases mv with
      | mk w r qmv =>
          cases w <;> cases r <;> simpa using hmv
    simpa [heq] using hq'
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨mv.next,
      List.mem_filter.mpr ⟨List.mem_finRange mv.next, h⟩, ?_⟩
    cases mv with
    | mk w r q =>
        cases w <;> cases r <;> simp

theorem sourceChoices_branch_iff (cut : Nat) (hcut : cut ≤ 6)
    (mv : Move) :
    mv ∈ sourceChoices cut ↔
      mv.next.val < cut ∨ (cut < 6 ∧ mv.next.val = cut) := by
  rw [sourceChoices_mem_iff]
  constructor <;> intro h <;> omega

/-- Set/list presentation of the exact child family in Enumerate62.v's
    expand. Existing labels have next<cut; the one fresh label has next=cut. -/
def sourceExpand (x : SourceNode) (slot : Slot) : List SourceNode :=
  (sourceChoices x.fresh).map (sourceChild x slot)

theorem sourceExpand_child_iff (x : SourceNode) (slot : Slot)
    (child : SourceNode) :
    child ∈ sourceExpand x slot ↔
      ∃ mv, mv.next.val ≤ x.fresh ∧ child = sourceChild x slot mv := by
  constructor
  · intro h
    obtain ⟨mv, hmv, hchild⟩ := List.mem_map.mp h
    subst child
    exact ⟨mv, (sourceChoices_mem_iff x.fresh mv).mp hmv, rfl⟩
  · rintro ⟨mv, hmv, rfl⟩
    exact List.mem_map.mpr
      ⟨mv, (sourceChoices_mem_iff x.fresh mv).mpr hmv, rfl⟩

def SourceWF (x : SourceNode) : Prop :=
  x.holes = sourceUndefCount x.tm ∧
  x.fresh ≤ 6 ∧
  sourceSupport x.tm x.fresh

theorem sourceRoot_wf : SourceWF sourceRoot := by
  refine ⟨?_, ?_, sourceRoot_support⟩
  · simp [sourceRoot, sourceRoot_holes]
  · decide

theorem sourceChild_wf (x : SourceNode) (slot : Slot) (mv : Move)
    (hwf : SourceWF x)
    (hhole : x.tm slot = none)
    (hslot : slot.1.val < x.fresh)
    (hdest : mv.next.val ≤ x.fresh) :
    SourceWF (sourceChild x slot mv) := by
  rcases hwf with ⟨hholes, hfresh, hsupport⟩
  refine ⟨?_, ?_, sourceChild_support x slot mv hsupport hslot hdest⟩
  · simp [sourceChild, sourceUndefCount_update x.tm slot mv hhole, hholes]
  · by_cases heq : mv.next.val = x.fresh
    · have hlt : x.fresh < 6 := by omega
      simp [sourceChild, sourceChildFresh, heq]
      omega
    · simp [sourceChild, sourceChildFresh, heq]
      exact hfresh

/-- Every node generated from node0 by the source expansion has the
    state-support invariant required by the weighted TNF proof. -/
inductive SourceReachable : SourceNode → Prop where
  | root : SourceReachable sourceRoot
  | child {x : SourceNode} {slot : Slot} {mv : Move}
      (hparent : SourceReachable x)
      (hhole : x.tm slot = none)
      (hslot : slot.1.val < x.fresh)
      (hdest : mv.next.val ≤ x.fresh) :
      SourceReachable (sourceChild x slot mv)

theorem sourceReachable_wf {x : SourceNode} (h : SourceReachable x) :
    SourceWF x := by
  induction h with
  | root => exact sourceRoot_wf
  | @child x slot mv hparent hhole hslot hdest ih =>
      exact sourceChild_wf x slot mv ih hhole hslot hdest

theorem sourceExpand_child_reachable {x : SourceNode} {slot : Slot}
    {child : SourceNode} (hparent : SourceReachable x)
    (hhole : x.tm slot = none) (hslot : slot.1.val < x.fresh)
    (hchild : child ∈ sourceExpand x slot) :
    SourceReachable child := by
  obtain ⟨mv, hdest, rfl⟩ := (sourceExpand_child_iff x slot child).mp hchild
  exact SourceReachable.child hparent hhole hslot hdest

/-- Direct source-to-certificate adapter for a non-last hole. The supplied
    child proofs are indexed exactly by the branches Enumerate62.v expands. -/
theorem source_expand_cover (B : Nat) (x : SourceNode) (n : Nat)
    (c : Config) (hreach : SourceReachable x)
    (hcut : 0 < x.fresh)
    (hroot : sourcePartial x.tm initialSlot =
      some (some ⟨true, true, (1 : Fin 6)⟩))
    (hrun : knownRun (sourcePartial x.tm) n = some c)
    (hhole : sourcePartial x.tm (readSlot c) = none)
    (hweight : ∀ d ∈ possibleDelays
      (refine (sourcePartial x.tm) (readSlot c) none) 0,
        d + n + 1 ≤ B)
    (hold : ∀ mv : Move, mv.next.val < x.fresh → ∀ m,
      compatible
        (sourcePartial (sourceChild x (readSlot c) mv).tm) m →
        WeightedBound B m)
    (hnew : ∀ q : Fin 6, q.val = x.fresh → ∀ w r : Bool, ∀ m,
      compatible
        (sourcePartial
          (sourceChild x (readSlot c) ⟨w, r, q⟩).tm) m →
        WeightedBound B m) :
    Cover (WeightedBound B) (sourcePartial x.tm) := by
  have hsupport : TNFSupport (sourcePartial x.tm) x.fresh :=
    sourceSupport_to_tnfSupport x.tm x.fresh (sourceReachable_wf hreach).2.2
  exact first_hole_tnf_cover B x.fresh (sourcePartial x.tm) n c
    hcut hsupport hroot hrun hhole hweight
    (by
      intro mv hlt m hm
      rw [sourceChild_partial] at hm
      exact hold mv hlt m hm)
    (by
      intro q hq w r m hm
      rw [sourceChild_partial] at hm
      exact hnew q hq w r m hm)

/-- The upstream expand' optimization: one remaining undefined row
    produces no ordinary children. -/
def sourceExpand' (x : SourceNode) (slot : Slot) : List SourceNode :=
  if x.holes = 1 then [] else sourceExpand x slot

theorem sourceExpand'_last_hole_empty (x : SourceNode) (slot : Slot)
    (hholes : x.holes = 1) :
    sourceExpand' x slot = [] := by
  simp [sourceExpand', hholes]

/-- If the source node has exactly one undefined transition and its first
    hole is reached by the blank run, the dropped ordinary completions are
    nonhalting and the explicit halt completion is weighted. This is the
    semantic justification for expand' returning []. -/
theorem source_last_hole_cover (B : Nat) (x : SourceNode) (n : Nat)
    (c : Config) (hreach : SourceReachable x) (hholes : x.holes = 1)
    (hroot : sourcePartial x.tm initialSlot =
      some (some ⟨true, true, (1 : Fin 6)⟩))
    (hrun : knownRun (sourcePartial x.tm) n = some c)
    (hhole : sourcePartial x.tm (readSlot c) = none)
    (hweight : ∀ d ∈ possibleDelays
      (refine (sourcePartial x.tm) (readSlot c) none) 0,
        d + n + 1 ≤ B) :
    Cover (WeightedBound B) (sourcePartial x.tm) := by
  have hwf := sourceReachable_wf hreach
  have hcount : sourceUndefCount x.tm = 1 := by omega
  have htmhole : x.tm (readSlot c) = none := by
    cases ht : x.tm (readSlot c) with
    | none => rfl
    | some mv => simp [sourcePartial, ht] at hhole
  have hrest : ∀ s, s ≠ readSlot c →
      ∃ mv, sourcePartial x.tm s = some (some mv) := by
    intro s hs
    obtain ⟨mv, hmv⟩ :=
      source_last_hole_rest x.tm (readSlot c) hcount htmhole s hs
    exact ⟨mv, by simp [sourcePartial, hmv]⟩
  exact .leaf _ (last_hole_sound B (sourcePartial x.tm) n c
    hroot hrun hhole hrest hweight)

#print axioms sourceSupport_to_tnfSupport
#print axioms sourceChild_partial
#print axioms sourceChild_support
#print axioms sourceChoices_mem_iff
#print axioms sourceExpand_child_iff
#print axioms sourceRoot_wf
#print axioms sourceReachable_wf
#print axioms sourceExpand_child_reachable
#print axioms source_expand_cover
#print axioms source_last_hole_cover

end BB6.Agent5Enumerate62
