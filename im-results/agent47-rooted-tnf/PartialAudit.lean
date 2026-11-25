import ThreeHoleAudit
import FourHoleResidualRoster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47PartialAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent8TNFPath

/-- Partial coverage trees preserve unresolved leaves explicitly. A closed
    subtree must pass the existing complete Audit checker. -/
inductive PartialAudit where
  | unresolved
  | closed (tree : Audit)
  | split (n : Nat) (s : Slot) (kids : Move → PartialAudit)

def partialCheck (B : Nat) (p : PartialMachine) : PartialAudit → Bool
  | .unresolved => true
  | .closed t => check B p t
  | .split n s kids => queryOK B p n s &&
      BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

def partialResiduals (p : PartialMachine) : PartialAudit → List (List Move × PartialMachine)
  | .unresolved => [([],p)]
  | .closed _ => []
  | .split _ s kids => BB6.Agent31FourHoleFrontier.allMoves.flatMap fun mv =>
      (partialResiduals (refine p s (some mv)) (kids mv)).map fun e => (mv :: e.1, e.2)
termination_by structural t => t

theorem partialSound (B : Nat) (p : PartialMachine) (t : PartialAudit)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : partialCheck B p t = true) :
    ∀ m, compatible p m → WeightedBound B m ∨
      ∃ e ∈ partialResiduals p t, compatible e.2 m := by
  induction t generalizing p with
  | unresolved =>
    intro m hm
    exact Or.inr ⟨([],p), by simp [partialResiduals], hm⟩
  | closed t =>
    intro m hm
    exact Or.inl ((certified B p t hf hno h).sound m hm)
  | split n s kids ih =>
    have hv : queryOK B p n s = true ∧ BB6.Agent31ThreeHole.allMoves
        (fun mv => partialCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [partialCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := queryOK_sound hv.1
    intro m hm
    cases ht : m s with
    | none =>
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
        have hs : readSlot c = s := by simpa [hr] using hread
        have hc : compatible (refine p s none) m := by
          simpa [ht] using compatible_refine p m s hm
        exact Or.inl (first_hole_weighted_halt B p n c hf hr
          (by simpa [hs] using hhole)
          (by simpa [hs] using weightOK_sound p s n B hw) m
          (by simpa [hs] using hc))
    | some mv =>
      have hc : compatible (refine p s (some mv)) m := by
        simpa [ht] using compatible_refine p m s hm
      have hchild := allMoves_sound _ hv.2 mv
      have hf' := refine_preserves_firstOne p s (some mv) hhole hf
      have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
      rcases ih mv (refine p s (some mv)) hf' hn' hchild m hc with hb | ⟨e,he,hec⟩
      · exact Or.inl hb
      · exact Or.inr ⟨(mv :: e.1,e.2), List.mem_flatMap.mpr
          ⟨mv, BB6.Agent31FourHoleFrontier.allMoves_complete mv, List.mem_map.mpr ⟨e,he,rfl⟩⟩,hec⟩

def byPartialMove (xs : List PartialAudit) (mv : Move) : PartialAudit :=
  xs[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD .unresolved

#print axioms partialSound
end BB6.Agent47PartialAudit
