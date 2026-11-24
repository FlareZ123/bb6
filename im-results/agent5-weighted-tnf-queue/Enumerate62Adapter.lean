import WeightedTNFCertificate

namespace BB6.Agent5Enumerate62
open BB6Coverage
open BB6.Agent13BlankDelay

/--
Faithful finite-state encoding of the pinned Enumerate62.v TNF node table.
Coq's A..F are Fin 6 in that order, S0/S1 are false/true, and L/R are
false/true. A missing source transition is an unexpanded slot; in the local
PartialMachine it is outer none, not an assigned halting transition.
-/
abbrev SourceTM := Slot → Option Move

def sourcePartial (tm : SourceTM) : PartialMachine :=
  fun s => (tm s).map (fun mv => some mv)

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
        simpa [sourcePartial, htm] using ht.symm
      subst t
      exact ⟨(hs s mv htm).1, by
        intro v hv
        cases hv
        exact (hs s mv htm).2⟩

/-- The 12 source table slots, in A0,A1,B0,B1,...,F0,F1 order. -/
def sourceAllSlots : List Slot :=
  (List.finRange 6).flatMap (fun q => [(q, false), (q, true)])

theorem sourceAllSlots_mem (s : Slot) : s ∈ sourceAllSlots := by
  rcases s with ⟨q, b⟩
  apply List.mem_flatMap.mpr
  refine ⟨q, List.mem_finRange q, ?_⟩
  cases b <;> simp

theorem sourceAllSlots_nodup : sourceAllSlots.Nodup := by
  decide

def sourceRootHoles : List Slot := sourceAllSlots.erase initialSlot

theorem sourceRootHoles_nodup : sourceRootHoles.Nodup := by
  exact sourceAllSlots_nodup.erase initialSlot

theorem sourceRootHoles_length : sourceRootHoles.length = 11 := by
  have hmem := sourceAllSlots_mem initialSlot
  have hlen : sourceAllSlots.length = 12 := by decide
  simp [sourceRootHoles, List.length_erase_of_mem hmem, hlen]

/-- The exact node0 table from Enumerate62.v:
    TM_from_str "1RB---_------_------_------_------_------". -/
def sourceRootTM : SourceTM :=
  fun s => if s = initialSlot then some ⟨true, true, (1 : Fin 6)⟩ else none

theorem sourceRoot_exact (s : Slot) :
    sourceRootTM s = none ↔ s ∈ sourceRootHoles := by
  by_cases hs : s = initialSlot
  · subst s
    constructor
    · simp [sourceRootTM]
    · intro h
      have hnot : initialSlot ∉ sourceRootHoles :=
        List.Nodup.not_mem_erase sourceAllSlots_nodup
      exact False.elim (hnot h)
  · have hmem : s ∈ sourceAllSlots := sourceAllSlots_mem s
    simp [sourceRootTM, sourceRootHoles, hs, hmem]

structure SourceNode where
  tm : SourceTM
  holes : List Slot
  fresh : Nat

def sourceRoot : SourceNode := ⟨sourceRootTM, sourceRootHoles, 2⟩

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

def SourceWF (x : SourceNode) : Prop :=
  x.holes.Nodup ∧
  (∀ s, x.tm s = none ↔ s ∈ x.holes) ∧
  x.fresh ≤ 6 ∧
  sourceSupport x.tm x.fresh

theorem sourceRoot_wf : SourceWF sourceRoot := by
  refine ⟨sourceRootHoles_nodup, ?_, ?_, sourceRoot_support⟩
  · intro s
    exact sourceRoot_exact s
  · decide

def sourceUpdate (tm : SourceTM) (slot : Slot) (mv : Move) : SourceTM :=
  fun s => if s = slot then some mv else tm s

def sourceChildFresh (x : SourceNode) (mv : Move) : Nat :=
  if mv.next.val = x.fresh then x.fresh + 1 else x.fresh

def sourceChild (x : SourceNode) (slot : Slot) (mv : Move) : SourceNode :=
  { tm := sourceUpdate x.tm slot mv
    holes := x.holes.erase slot
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
      exact hv.symm
    subst v
    exact ⟨Nat.lt_of_lt_of_le hslot (sourceChildFresh_ge x mv),
      sourceChildFresh_gt_dest x mv hdest⟩
  · have htm : x.tm s = some v := by
      simpa [sourceChild, sourceUpdate, he] using hv
    obtain ⟨hsrc, hdst⟩ := hs s v htm
    have hle := sourceChildFresh_ge x mv
    exact ⟨Nat.lt_of_lt_of_le hsrc hle, Nat.lt_of_lt_of_le hdst hle⟩

theorem sourceChild_holes_length (x : SourceNode) (slot : Slot) (mv : Move)
    (hwf : SourceWF x) (hhole : x.tm slot = none) :
    (sourceChild x slot mv).holes.length = x.holes.length - 1 := by
  rcases hwf with ⟨hnodup, hexact, _, _⟩
  have hmem : slot ∈ x.holes := (hexact slot).mp hhole
  have hlen : (x.holes.erase slot).length = x.holes.length - 1 :=
    List.length_erase_of_mem hmem
  simpa [sourceChild] using hlen

theorem sourceChild_wf (x : SourceNode) (slot : Slot) (mv : Move)
    (hwf : SourceWF x)
    (hhole : x.tm slot = none)
    (hslot : slot.1.val < x.fresh)
    (hdest : mv.next.val ≤ x.fresh) :
    SourceWF (sourceChild x slot mv) := by
  rcases hwf with ⟨hnodup, hexact, hfresh, hsupport⟩
  refine ⟨hnodup.erase slot, ?_, ?_, sourceChild_support x slot mv hsupport hslot hdest⟩
  · intro s
    by_cases hs : s = slot
    · subst s
      constructor
      · simp [sourceChild, sourceUpdate]
      · intro h
        have hnot : slot ∉ x.holes.erase slot := List.Nodup.not_mem_erase hnodup
        exact False.elim (hnot h)
    · simp [sourceChild, sourceUpdate, hs, hexact s]
  · by_cases heq : mv.next.val = x.fresh
    · have hlt : x.fresh < 6 := by omega
      simp [sourceChild, sourceChildFresh, heq]
      omega
    · simp [sourceChild, sourceChildFresh, heq]
      exact hfresh

/-- The source's nested loops enumerate four write/direction choices for
    every old label below cut, plus four choices for the least fresh label
    equal to cut. -/
def sourceChoices (cut : Nat) : List Move :=
  (List.finRange 6).flatMap (fun q =>
    if q.val ≤ cut then
      [⟨false, false, q⟩, ⟨false, true, q⟩,
       ⟨true, false, q⟩, ⟨true, true, q⟩]
    else [])

theorem sourceChoices_mem_iff (cut : Nat) (mv : Move) :
    mv ∈ sourceChoices cut ↔ mv.next.val ≤ cut := by
  constructor
  · intro h
    obtain ⟨q, hq, hmv⟩ := List.mem_flatMap.mp h
    have hqle : q.val ≤ cut := by
      by_cases hle : q.val ≤ cut
      · exact hle
      · have hfalse : False := by simpa [hle] using hmv
        exact False.elim hfalse
    have hmv' : mv ∈
        [⟨false, false, q⟩, ⟨false, true, q⟩,
         ⟨true, false, q⟩, ⟨true, true, q⟩] := by
      simpa [hqle] using hmv
    have heq : mv.next = q := by
      cases mv with
      | mk w r qmv =>
          cases w <;> cases r <;> simpa using hmv'
    simpa [heq] using hqle
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨mv.next, List.mem_finRange mv.next, ?_⟩
    cases mv with
    | mk w r q =>
        cases w <;> cases r <;> simp [h]

theorem sourceChoices_branch_iff (cut : Nat)
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
    sourceSupport_to_tnfSupport x.tm x.fresh (sourceReachable_wf hreach).2.2.2
  exact first_hole_tnf_cover B x.fresh (sourcePartial x.tm) n c
    hcut hsupport hroot hrun hhole hweight
    (by
      intro mv hlt m hm
      rw [← sourceChild_partial] at hm
      exact hold mv hlt m hm)
    (by
      intro q hq w r m hm
      rw [← sourceChild_partial] at hm
      exact hnew q hq w r m hm)

/-- The upstream expand' optimization: one remaining undefined row
    produces no ordinary children. -/
def sourceExpand' (x : SourceNode) (slot : Slot) : List SourceNode :=
  if x.holes.length = 1 then [] else sourceExpand x slot

theorem sourceExpand'_last_hole_empty (x : SourceNode) (slot : Slot)
    (hholes : x.holes.length = 1) :
    sourceExpand' x slot = [] := by
  simp [sourceExpand', hholes]

/-- If the source node has exactly one undefined transition and its first
    hole is reached by the blank run, the dropped ordinary completions are
    nonhalting and the explicit halt completion is weighted. This is the
    semantic justification for expand' returning []. -/
theorem source_last_hole_cover (B : Nat) (x : SourceNode) (n : Nat)
    (c : Config) (hreach : SourceReachable x)
    (hholes : x.holes.length = 1)
    (hroot : sourcePartial x.tm initialSlot =
      some (some ⟨true, true, (1 : Fin 6)⟩))
    (hrun : knownRun (sourcePartial x.tm) n = some c)
    (hhole : sourcePartial x.tm (readSlot c) = none)
    (hweight : ∀ d ∈ possibleDelays
      (refine (sourcePartial x.tm) (readSlot c) none) 0,
        d + n + 1 ≤ B) :
    Cover (WeightedBound B) (sourcePartial x.tm) := by
  rcases sourceReachable_wf hreach with ⟨_, hexact, _, _⟩
  have htmhole : x.tm (readSlot c) = none := by
    cases ht : x.tm (readSlot c) with
    | none => rfl
    | some mv => simp [sourcePartial, ht] at hhole
  have hmem : readSlot c ∈ x.holes := (hexact (readSlot c)).mp htmhole
  have hsingle : x.holes = [readSlot c] := by
    cases hlist : x.holes with
    | nil =>
        simp [hlist] at hholes
    | cons a tail =>
        cases tail with
        | nil =>
            have ha : a = readSlot c := by
              have hmem' : readSlot c ∈ [a] := by simpa [hlist] using hmem
              simpa using hmem'.symm
            simp [hlist, ha]
        | cons b rest =>
            simp [hlist] at hholes
  have hrest : ∀ s, s ≠ readSlot c →
      ∃ mv, sourcePartial x.tm s = some (some mv) := by
    intro s hs
    have hnotmem : s ∉ x.holes := by
      rw [hsingle]
      simp [hs]
    have hnotnone : x.tm s ≠ none := by
      intro ht
      exact hnotmem ((hexact s).mp ht)
    cases ht : x.tm s with
    | none => exact False.elim (hnotnone ht)
    | some mv => exact ⟨mv, by simp [sourcePartial, ht]⟩
  exact .leaf _ (last_hole_sound B (sourcePartial x.tm) n c
    hroot hrun hhole hrest hweight)

#print axioms sourceSupport_to_tnfSupport
#print axioms sourceRoot_wf
#print axioms sourceChild_partial
#print axioms sourceChild_support
#print axioms sourceChild_holes_length
#print axioms sourceChoices_mem_iff
#print axioms sourceExpand_child_iff
#print axioms sourceReachable_wf
#print axioms sourceExpand_child_reachable
#print axioms source_expand_cover
#print axioms source_last_hole_cover

end BB6.Agent5Enumerate62
