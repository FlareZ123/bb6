import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32PartialCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

/-- A partial proof tree. A retained leaf is an explicit proof obligation. -/
inductive Cut where
  | keep
  | closed (audit : Audit)
  | split (n : Nat) (s : Slot) (kids : Move → Cut)

def moves : List Move := (List.finRange 6).flatMap fun q =>
  [false,true].flatMap fun w => [false,true].map fun r => ⟨w,r,q⟩

theorem moves_complete (mv : Move) : mv ∈ moves := by
  rcases mv with ⟨w,r,q⟩
  unfold moves
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨w,by cases w <;> simp,?_⟩
  exact List.mem_map.mpr ⟨r,by cases r <;> simp,rfl⟩

def checkCut (B : Nat) (p : PartialMachine) : Cut → Bool
  | .keep => true
  | .closed a => zipCheck B p a
  | .split n s kids => zipQueryOK B p n s && allMoves (fun mv =>
      checkCut B (refine p s (some mv)) (kids mv))
termination_by structural t => t

def retained (p : PartialMachine) : Cut → List PartialMachine
  | .keep => [p]
  | .closed _ => []
  | .split _ s kids => moves.flatMap fun mv => retained (refine p s (some mv)) (kids mv)
termination_by structural t => t

theorem haltAtQuery (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hr : p initialSlot = some (some ⟨true,true,1⟩))
    (h : zipQueryOK B p n s = true) :
    ∀ m, compatible (refine p s none) m → WeightedBound B m := by
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound h
  cases hk : knownRun p n with
  | none => simp [hk] at hread
  | some c =>
    have hs : readSlot c = s := by simpa [hk] using hread
    intro m hm
    exact first_hole_weighted_halt B p n c hr hk
      (by simpa [hs] using hhole)
      (by simpa [hs] using weightOK_sound p s n B hw) m
      (by simpa only [hs] using hm)

theorem cut_sound (B : Nat) (p : PartialMachine) (t : Cut)
    (hr : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p)
    (hc : checkCut B p t = true)
    (m : Machine) (hm : compatible p m) :
    WeightedBound B m ∨ ∃ q ∈ retained p t, compatible q m := by
  induction t generalizing p with
  | keep => exact Or.inr ⟨p,by simp [retained],hm⟩
  | closed a => exact Or.inl ((certifiedZip B p a hr hn hc).sound m hm)
  | split n s kids ih =>
    have hh : zipQueryOK B p n s = true ∧
        allMoves (fun mv => checkCut B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [checkCut, Bool.and_eq_true] using hc
    have hu := (zipQueryOK_sound hh.1).2.1
    obtain ⟨v,_,hv⟩ := child_cover p m s hm hu
    cases v with
    | none => exact Or.inl (haltAtQuery B p n s hr hh.1 m hv)
    | some mv =>
      have hh' := allMoves_sound _ hh.2 mv
      have hr' := refine_preserves_firstOne p s (some mv) hu hr
      have hn' := weightedTNFNoAssignedHalt_refine p s mv hn
      rcases ih mv (refine p s (some mv)) hr' hn' hh' hv with h | ⟨q,hq,hcomp⟩
      · exact Or.inl h
      · exact Or.inr ⟨q,List.mem_flatMap.mpr ⟨mv,moves_complete mv,hq⟩,hcomp⟩

theorem cut_cover (B : Nat) (p : PartialMachine) (t : Cut)
    (hr : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p)
    (hc : checkCut B p t = true)
    (leaves : ∀ q ∈ retained p t, Cover (WeightedBound B) q) : Cover (WeightedBound B) p := by
  refine .leaf p ?_
  intro m hm
  rcases cut_sound B p t hr hn hc m hm with h | ⟨q,hq,hcomp⟩
  · exact h
  · exact (leaves q hq).sound m hcomp

def byMoveCut (xs : List Cut) (mv : Move) : Cut :=
  xs[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD .keep

/-- Only canonical introductions are explored. A fresh successor represents
all unused labels by a root-fixing permutation, preserving weighted score. -/
def tnfMoves (cut : Nat) : List Move :=
  moves.filter (fun mv => decide (mv.next.val ≤ cut))

theorem mem_tnfMoves (cut : Nat) (mv : Move) (h : mv.next.val ≤ cut) :
    mv ∈ tnfMoves cut := List.mem_filter.mpr ⟨moves_complete mv,by simpa using h⟩

def tnfCheck (B cut : Nat) (p : PartialMachine) : Cut → Bool
  | .keep => true
  | .closed a => zipCheck B p a
  | .split n s kids => zipQueryOK B p n s && allMoves (fun mv =>
      if mv.next.val ≤ cut then
        tnfCheck B (advanceCut cut mv) (refine p s (some mv)) (kids mv)
      else true)
termination_by structural t => t

def tnfRetained (cut : Nat) (p : PartialMachine) : Cut → List PartialMachine
  | .keep => [p]
  | .closed _ => []
  | .split _ s kids => (tnfMoves cut).flatMap fun mv =>
      tnfRetained (advanceCut cut mv) (refine p s (some mv)) (kids mv)
termination_by structural t => t

theorem tnfCut_cover (B cut : Nat) (p : PartialMachine) (t : Cut)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hr : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p)
    (hc : tnfCheck B cut p t = true)
    (leaves : ∀ q ∈ tnfRetained cut p t, Cover (WeightedBound B) q) :
    Cover (WeightedBound B) p := by
  induction t generalizing p cut with
  | keep => exact leaves p (by simp [tnfRetained])
  | closed a => exact .leaf p ((certifiedZip B p a hr hn hc).sound)
  | split n s kids ih =>
    have hh : zipQueryOK B p n s = true ∧ allMoves (fun mv =>
        if mv.next.val ≤ cut then tnfCheck B (advanceCut cut mv)
          (refine p s (some mv)) (kids mv) else true) = true := by
      simpa only [tnfCheck,Bool.and_eq_true] using hc
    obtain ⟨hread,hu,_⟩ := zipQueryOK_sound hh.1
    have hslot : s.1.val < cut := by
      cases hk : knownRun p n with
      | none => simp [hk] at hread
      | some c =>
        have he : readSlot c = s := by simpa [hk] using hread
        rw [← he]
        exact knownRun_support p cut hcut hs n c hk
    have hchild : ∀ mv : Move, mv.next.val ≤ cut →
        Cover (WeightedBound B) (refine p s (some mv)) := by
      intro mv hm
      have hc' : tnfCheck B (advanceCut cut mv) (refine p s (some mv)) (kids mv) = true := by
        simpa only [if_pos hm] using allMoves_sound _ hh.2 mv
      have hg : cut ≤ advanceCut cut mv := by unfold advanceCut; split <;> omega
      have hmv : mv.next.val < advanceCut cut mv := by unfold advanceCut; split <;> omega
      have hs' := refine_support p s mv cut (advanceCut cut mv) hs hg (by omega) hmv
      apply ih mv (advanceCut cut mv) (refine p s (some mv)) (by omega) hs'
        (refine_preserves_firstOne p s (some mv) hu hr)
        (weightedTNFNoAssignedHalt_refine p s mv hn) hc'
      intro q hq
      apply leaves q
      exact List.mem_flatMap.mpr ⟨mv,mem_tnfMoves cut mv hm,hq⟩
    exact .leaf p (tnf_branch_sound B cut p s hcut hs hu hslot hr
      (haltAtQuery B p n s hr hh.1)
      (fun mv hm => (hchild mv (by omega)).sound)
      (fun q hq w r => (hchild ⟨w,r,q⟩ (by simp [hq])).sound))

#print axioms tnfCut_cover
#print axioms cut_sound
#print axioms cut_cover
end BB6.Agent32PartialCut
