import SourceQueueImplication
import Enumerate62Potential

namespace BB6.Agent32SourceDrain
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5Enumerate62
open BB6.Agent13QueueCoverage BB6.Agent32SourceQueue

abbrev PNode := BB6.Agent48Queue.Node
abbrev PWeight := BB6.Agent48Queue.weight
abbrev PMass := BB6.Agent48Queue.mass
abbrev POld := BB6.Agent48Queue.existingChild
abbrev PNew := BB6.Agent48Queue.freshChild

def project (x : SourceNode) : PNode :=
  ⟨x.holes.length, ⟨x.fresh % 7, Nat.mod_lt _ (by decide)⟩⟩

theorem project_cut (x : SourceNode) (hx : SourceReachable x) :
    (project x).cut.val = x.fresh := by
  have h := (sourceReachable_wf hx).2.2.1
  exact Nat.mod_eq_of_lt (by omega)

/-- Check only the finite choice ordering, independently of the source table. -/
theorem choice_tags (cut : Fin 7) :
    (sourceChoices cut.val).map (fun mv => decide (mv.next.val = cut.val)) =
      List.replicate (4*cut.val) false ++ (if cut.val < 6 then List.replicate 4 true else []) := by
  revert cut
  decide

theorem project_child (x : SourceNode) (slot : Slot) (mv : Move)
    (hx : SourceReachable x) (hh : x.tm slot = none) :
    project (sourceChild x slot mv) =
      if mv.next.val = x.fresh then PNew (project x) else POld (project x) := by
  have hl := sourceChild_holes_length x slot mv (sourceReachable_wf hx) hh
  change BB6.Agent48Queue.Node.mk (sourceChild x slot mv).holes.length _ = _
  rw [hl]
  by_cases h : mv.next.val = x.fresh
  · simp [h, BB6.Agent48Queue.freshChild, project, sourceChild, sourceChildFresh]
  · simp [h, BB6.Agent48Queue.existingChild, project, sourceChild, sourceChildFresh]

theorem project_expand (x : SourceNode) (slot : Slot)
    (hx : SourceReachable x) (hh : x.tm slot = none) :
    (sourceExpand x slot).map project = BB6.Agent48Queue.expandProjection (project x) := by
  rw [sourceExpand, List.map_map]
  have hc := project_cut x hx
  calc
    (sourceChoices x.fresh).map (project ∘ sourceChild x slot) =
      (sourceChoices (project x).cut.val).map (fun mv => if mv.next.val = (project x).cut.val then PNew (project x) else POld (project x)) := by
        rw [hc]
        apply List.map_congr_left
        intro mv _
        exact project_child x slot mv hx hh
    _ = ((sourceChoices (project x).cut.val).map (fun mv => decide (mv.next.val = (project x).cut.val))).map (fun b => if b then PNew (project x) else POld (project x)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro mv _
        simp
    _ = BB6.Agent48Queue.expandProjection (project x) := by
        rw [choice_tags]
        simp only [BB6.Agent48Queue.expandProjection, List.map_append, List.map_replicate, Bool.false_eq_true, ite_false]
        by_cases h : (project x).cut.val < 6 <;> simp [h]

theorem project_expand' (x : SourceNode) (slot : Slot)
    (hx : SourceReachable x) (hh : x.tm slot = none) (hpos : 1 ≤ (project x).holes) :
    (sourceExpand' x slot).map project = BB6.Agent48Queue.expandProjection' (project x) hpos := by
  by_cases h : x.holes.length = 1
  · simp [sourceExpand', BB6.Agent48Queue.expandProjection', project, h]
  · simpa [sourceExpand', BB6.Agent48Queue.expandProjection', project, h] using project_expand x slot hx hh

def mass (xs : List SourceNode) : Nat := PMass (xs.map project)
def reachableList (xs : List SourceNode) : Prop := ∀ x, x ∈ xs → SourceReachable x

theorem mass_nil : mass [] = 0 := rfl
theorem mass_cons (x : SourceNode) (xs : List SourceNode) :
    mass (x :: xs) = PWeight (project x) + mass xs := rfl

theorem mass_append (xs ys : List SourceNode) : mass (xs++ys) = mass xs + mass ys := by
  simp [mass, BB6.Agent48Queue.mass_append]

theorem reachable_append (xs ys : List SourceNode) (hx : reachableList xs) (hy : reachableList ys) :
    reachableList (xs++ys) := by
  intro x h
  rcases List.mem_append.mp h with h|h
  · exact hx x h
  · exact hy x h

theorem reachable_cons (x : SourceNode) (xs : List SourceNode) (hx : SourceReachable x) (hs : reachableList xs) : reachableList (x::xs) := by
  intro y h
  rcases List.mem_cons.mp h with h|h
  · cases h; exact hx
  · exact hs y h

/-- Local projected decrease. The decision remains dependent on the entire
source table, so there is no invalid assumption that it factors through
(holes,cut). -/
theorem halt_children (H : Nat) (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) (x : SourceNode) (hx : SourceReachable x)
    (ys : List SourceNode) (hd : decide x = .halt ys) :
    reachableList ys ∧ mass ys < PWeight (project x) := by
  have h := he x hx
  rw [hd] at h
  obtain ⟨n,c,hr,hh,hn,hys⟩ := h
  have hhole : x.tm (readSlot c) = none := by
    cases ht : x.tm (readSlot c) with
    | none => rfl
    | some mv => simp [sourcePartial, ht] at hh
  have hp : 1 ≤ (project x).holes := by
    have hm := ((sourceReachable_wf hx).2.1 _).mp hhole
    exact List.length_pos_of_mem hm
  have hs : (readSlot c).1.val < x.fresh :=
    knownRun_support _ _ (reachable_cut_positive hx)
      (sourceSupport_to_tnfSupport x.tm x.fresh (sourceReachable_wf hx).2.2.2) n c hr
  rw [hys]
  constructor
  · intro y hy
    by_cases hlast : x.holes.length = 1
    · simp [sourceExpand', hlast] at hy
    · rw [sourceExpand', ite_eq_right hlast] at hy
      obtain ⟨mv,hm,rfl⟩ := (sourceExpand_child_iff _ _ _).mp hy
      exact SourceReachable.child hx hhole hs hm
  · unfold mass
    rw [project_expand' x (readSlot c) hx hhole hp]
    exact BB6.Agent48Queue.expandProjection'_mass_lt (project x) hp

/-- Lift Agent48's local potential inequality through the payload queue. -/
theorem bfsAux_bound (H : Nat) (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) :
    ∀ xs hold, reachableList xs → reachableList hold →
      reachableList (bfsAux decide xs hold) ∧
      mass (bfsAux decide xs hold) ≤ mass xs + mass hold := by
  intro xs
  induction xs with
  | nil => intro hold _ hh; simpa [bfsAux, mass_nil] using And.intro hh (Nat.le_refl (mass hold))
  | cons x xs ih =>
    intro hold hx hh
    have hr := hx x (by simp)
    have ht : reachableList xs := fun y hy => hx y (by simp [hy])
    cases hd : decide x with
    | halt children =>
      obtain ⟨hc,hw⟩ := halt_children H decide he x hr children hd
      obtain ⟨hreach,hbound⟩ := ih (children++hold) ht (reachable_append _ _ hc hh)
      simp only [bfsAux, bfsHoldAfter, hd]
      refine ⟨hreach, ?_⟩
      rw [mass_append] at hbound
      rw [mass_cons]
      omega
    | nonhalt =>
      obtain ⟨hreach,hbound⟩ := ih hold ht hh
      simp only [bfsAux, bfsHoldAfter, hd]
      refine ⟨hreach, ?_⟩
      rw [mass_cons]
      omega
    | unknown =>
      obtain ⟨hreach,hbound⟩ := ih (x::hold) ht (reachable_cons _ _ hr hh)
      simp only [bfsAux, bfsHoldAfter, hd]
      refine ⟨hreach, ?_⟩
      rw [mass_cons] at hbound ⊢
      omega

def totalMass (q : CoverageQueue SourceNode) : Nat := mass q.active + mass q.holdout
def reachableQueue (q : CoverageQueue SourceNode) : Prop := reachableList q.active ∧ reachableList q.holdout

theorem bfsRound_bound (H : Nat) (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) (q : CoverageQueue SourceNode) (hq : reachableQueue q) :
    reachableQueue (bfsRound decide q) ∧ totalMass (bfsRound decide q) ≤ totalMass q := by
  obtain ⟨hr,hm⟩ := bfsAux_bound H decide he q.active q.holdout hq.1 hq.2
  refine ⟨⟨hr, ?_⟩, ?_⟩
  · intro x h; simp [bfsRound] at h
  · simpa [totalMass,bfsRound,mass_nil] using hm

theorem q0_bound (H : Nat) (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) :
    reachableQueue (q0 decide sourceRoot) ∧ totalMass (q0 decide sourceRoot) ≤ 25^11 := by
  have hroot : reachableQueue (rootQueue sourceRoot) := by
    constructor
    · intro x h; simp [rootQueue] at h; subst x; exact SourceReachable.root
    · intro x h; simp [rootQueue] at h
  have hm : totalMass (rootQueue sourceRoot) = 25^11 := by
    simp [totalMass, rootQueue, mass_cons, mass_nil, project, sourceRoot, sourceRootHoles_length, BB6.Agent48Queue.weight]
  let q := rootQueue sourceRoot
  have h1 := bfsRound_bound H decide he q hroot
  have h2 := bfsRound_bound H decide he _ h1.1
  have h3 := bfsRound_bound H decide he _ h2.1
  have h4 := bfsRound_bound H decide he _ h3.1
  refine ⟨h4.1, ?_⟩
  change totalMass (bfsRound decide (bfsRound decide (bfsRound decide (bfsRound decide q)))) ≤ _
  change totalMass q = _ at hm
  omega

theorem update_bound (H : Nat) (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) (q : CoverageQueue SourceNode)
    (hq : reachableList q.active) (hne : q.active ≠ []) :
    reachableList (update decide q).active ∧ mass (update decide q).active < mass q.active := by
  cases hq' : q.active with
  | nil => exact False.elim (hne hq')
  | cons x xs =>
    have hx : SourceReachable x := hq x (by simp [hq'])
    have hs : reachableList xs := fun y hy => hq y (by simp [hq',hy])
    have hp := BB6.Agent48Queue.weight_pos (project x)
    cases hd : decide x with
    | halt children =>
      obtain ⟨hc,hw⟩ := halt_children H decide he x hx children hd
      simp only [update,hq',hd]
      refine ⟨reachable_append _ _ hc hs, ?_⟩
      rw [mass_append,mass_cons]
      omega
    | nonhalt =>
      simp only [update,hq',hd]
      refine ⟨hs, ?_⟩
      rw [mass_cons]
      exact Nat.lt_add_of_pos_left hp
    | unknown =>
      simp only [update,hq',hd]
      refine ⟨hs, ?_⟩
      rw [mass_cons]
      exact Nat.lt_add_of_pos_left hp

theorem runUpdates_drains (H : Nat) (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) (fuel : Nat) (q : CoverageQueue SourceNode)
    (hr : reachableList q.active) (hm : mass q.active ≤ fuel) :
    (runUpdates decide fuel q).active = [] := by
  induction fuel generalizing q with
  | zero =>
    have hzero : mass q.active = 0 := by omega
    have hmap := (BB6.Agent48Queue.mass_zero_iff_nil (q.active.map project)).mp hzero
    have hnil : q.active = [] := by simpa using hmap
    simp [runUpdates,hnil]
  | succ fuel ih =>
    cases hq : q.active with
    | nil => simp [runUpdates,hq]
    | cons x xs =>
      obtain ⟨hr',hm'⟩ := update_bound H decide he q hr (by simp [hq])
      have hnext : mass (update decide q).active ≤ fuel := by omega
      simpa [runUpdates,hq] using ih (update decide q) hr' hnext

theorem every_source_chunk_drains (H : Nat) (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) (l sz : Nat) :
    (runUpdates decide BB6.Agent48Queue.maxT (chunkQueue (q0 decide sourceRoot) l sz)).active = [] := by
  obtain ⟨hr,hm⟩ := q0_bound H decide he
  apply runUpdates_drains H decide he
  · intro x hx
    exact hr.1 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · have hchunk := BB6.Agent48Queue.mass_chunk_le ((q0 decide sourceRoot).active.map project) l sz
    have hmax := BB6.Agent48Queue.maxT_ge_25_pow_11
    simp only [chunkQueue,mass,List.map_take,List.map_drop]
    change PMass (((q0 decide sourceRoot).active.map project).drop l |>.take sz) ≤ _
    change mass (q0 decide sourceRoot).active + mass (q0 decide sourceRoot).holdout ≤ 25^11 at hm
    exact Nat.le_trans hchunk (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) hm) hmax)

theorem source_queue_root_cover_maxT (H B : Nat) (hB : H+6 ≤ B)
    (decide : SourceNode → QueueDecision SourceNode)
    (he : SourceEvidence H decide) (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide sourceRoot) ranges)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide BB6.Agent48Queue.maxT (chunkQueue (q0 decide sourceRoot) r.1 r.2)).holdout → SourceSafe B y) :
    Cover (WeightedBound B) (sourcePartial sourceRoot.tm) :=
  source_queue_root_cover H B hB decide he ranges hpart BB6.Agent48Queue.maxT
    (fun r _ => every_source_chunk_drains H decide he r.1 r.2) hcert

#print axioms project_expand'
#print axioms halt_children
#print axioms every_source_chunk_drains
#print axioms source_queue_root_cover_maxT
end BB6.Agent32SourceDrain
