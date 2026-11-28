import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45ZipHybrid
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit

inductive Hybrid (B : Nat) where
  | closed (tree : Audit)
  | covered (q : PartialMachine) (safe : Cover (WeightedBound B) q)
  | split (n : Nat) (s : Slot) (kids : Move → Hybrid B)

def check (B : Nat) (p : PartialMachine) : Hybrid B → Bool
  | .closed t => zipCheck B p t
  | .covered q _ => tableOK p q
  | .split n s kids => zipQueryOK B p n s &&
      allMoves (fun mv => check B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem sound (B : Nat) (p : PartialMachine) (t : Hybrid B)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p) (h : check B p t = true) :
    Cover (WeightedBound B) p := by
  induction t generalizing p with
  | closed t => exact .leaf p (certifiedZip B p t hf hn h).sound
  | covered q safe =>
    have he : p = q := tableOK_sound p q h
    subst q
    exact safe
  | split n s kids ih =>
    have hv : zipQueryOK B p n s = true ∧
        allMoves (fun mv => check B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [check, Bool.and_eq_true] using h
    obtain ⟨hread, hhole, hw⟩ := zipQueryOK_sound hv.1
    apply Cover.leaf
    intro m hm
    cases ht : m s with
    | none =>
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
        have hs : readSlot c = s := by simpa [hr] using hread
        have hc : compatible (refine p s none) m := by
          simpa [ht] using compatible_refine p m s hm
        exact first_hole_weighted_halt B p n c hf hr
          (by simpa [hs] using hhole)
          (by simpa [hs] using weightOK_sound p s n B hw) m
          (by simpa [hs] using hc)
    | some mv =>
      have hc : compatible (refine p s (some mv)) m := by
        simpa [ht] using compatible_refine p m s hm
      exact (ih mv (refine p s (some mv))
        (refine_preserves_firstOne p s (some mv) hhole hf)
        (weightedTNFNoAssignedHalt_refine p s mv hn)
        (allMoves_sound _ hv.2 mv)).sound m hc

def byHybridMove {B : Nat} (xs : List (Hybrid B)) (mv : Move) : Hybrid B :=
  xs[12*mv.write.toNat + 6*mv.right.toNat + mv.next.val]?.getD
    (.closed (.last 0 (0,false)))

#print axioms sound
end BB6.Agent24Raw45ZipHybrid
