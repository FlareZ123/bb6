import FastThreeHoleAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent14ConditionalHybrid
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10FastAudit

/-- A first-hole certificate may depend on an explicit proposition. The executable
    checker ignores proofs, including the implication carried by a covered leaf. -/
inductive Hybrid (B : Nat) (P : Prop) where
  | closed (tree : Audit)
  | covered (q : PartialMachine) (safe : P → Cover (WeightedBound B) q)
  | split (n : Nat) (s : Slot) (kids : Move → Hybrid B P)

def check (B : Nat) {P : Prop} (p : PartialMachine) : Hybrid B P → Bool
  | .closed t => fastCheck B p t
  | .covered q _ => tableOK p q
  | .split n s kids => queryOK B p n s && allMoves (fun mv => check B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem sound (B : Nat) {P : Prop} (p : PartialMachine) (t : Hybrid B P)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p) (h : check B p t = true) :
    P → Cover (WeightedBound B) p := by
  intro hp
  induction t generalizing p with
  | closed t => exact .leaf p (certifiedFast B p t hf hn h).sound
  | covered q safe =>
    have he : p = q := tableOK_sound p q h
    subst q; exact safe hp
  | split n s kids ih =>
    have hv : queryOK B p n s = true ∧ allMoves (fun mv => check B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [check,Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := queryOK_sound hv.1
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
        (weightedTNFNoAssignedHalt_refine p s mv hn) (allMoves_sound _ hv.2 mv)).sound m hc

def byHybridMove {B : Nat} {P : Prop} (xs : List (Hybrid B P)) (mv : Move) : Hybrid B P :=
  xs[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD (.closed (.last 0 (0,false)))

theorem fromCodes_nohalt (xs : List Nat) : weightedTNFNoAssignedHalt (BB6Coverage.FAR.fromCodes xs) := by
  intro s
  unfold BB6Coverage.FAR.fromCodes
  rcases s with ⟨q,b⟩
  cases h : xs[2*q.val+b.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h,hn]

#print axioms sound
end BB6.Agent14ConditionalHybrid
