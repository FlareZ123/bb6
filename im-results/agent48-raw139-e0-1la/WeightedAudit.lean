import PackedPrefixAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48WeightedAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedAudit BB6.Agent48PackedPrefix

inductive WeightedAudit (B : Nat) : Type
  | ordinary (t : Audit)
  | bounded (p : PartialMachine) (safe : ∀ m, compatible p m → WeightedBound B m)
  | split (n : Nat) (s : Slot) (kids : Move → WeightedAudit B)

def check (B : Nat) (p : PartialMachine) : WeightedAudit B → Bool
  | .ordinary t => packedPrefixCheck B p t
  | .bounded q _ => tableOK p q
  | .split n s kids => packedQueryOK B p n s &&
      allMoves (fun mv => check B (refine p s (some mv)) (kids mv))
termination_by structural t => t

noncomputable def certified (B : Nat) (p : PartialMachine) (t : WeightedAudit B)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : check B p t = true) : WeightedTNFCertificate B p 6 := by
  induction t generalizing p with
  | ordinary t =>
    exact certifiedPacked B p t hroot hno (by simpa only [check,packedPrefixCheck_eq] using h)
  | bounded q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [check] using h)
    subst q
    exact .weightedLeaf hroot (support6 p) hno safe
  | split n s kids ih =>
    have hv : packedQueryOK B p n s = true ∧
        allMoves (fun mv => check B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [check, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := packedQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      refine .expand hroot (support6 p) (by decide) hno hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p s n B hw) ?_ ?_
      · intro mv _
        have hchild := allMoves_sound _ hv.2 mv
        have hr' := refine_preserves_firstOne p s (some mv) hhole hroot
        have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
        simpa only [hs] using ih mv (refine p s (some mv)) hr' hn' hchild
      · intro q hq _ _
        have hlt := q.isLt
        omega

#print axioms certified
end BB6.Agent48WeightedAudit
