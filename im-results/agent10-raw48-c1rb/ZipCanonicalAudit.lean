import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10CanonicalAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

def nextCut (cut : Nat) (mv : Move) : Nat := if mv.next.val < cut then cut else cut+1

def canonicalCheck (B : Nat) (p : PartialMachine) (cut : Nat) : Audit → Bool
  | .last n s => zipQueryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && zipCycle p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => zipQueryOK B p n s && allMoves (fun mv =>
      if mv.next.val ≤ cut then canonicalCheck B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true)
termination_by structural t => t

noncomputable def certifiedCanonical (B : Nat) (p : PartialMachine) (cut : Nat) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (hsupport : TNFSupport p cut) (hcut : 0 < cut)
    (h : canonicalCheck B p cut t = true) : WeightedTNFCertificate B p cut := by
  induction t generalizing p cut with
  | last n s =>
    have hv : zipQueryOK B p n s = true ∧ restOK p s = true := by
      simpa only [canonicalCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      exact .lastHole hroot hsupport hcut hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using restOK_sound p s hv.2)
        (by simpa [hs] using weightOK_sound p s n B hw)
  | cycle e k r b =>
    have hv : 0 < k ∧ zipCycle p e k r b = true := by
      simpa only [canonicalCheck, Bool.and_eq_true, decide_eq_true_eq] using h
    exact .nonhalt hroot hsupport hno (zipCycle_sound p e k r b hv.1 hv.2)
  | far rev d C =>
    exact .nonhalt hroot hsupport hno (farSound p rev C (by simpa only [canonicalCheck] using h))
  | proven q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [canonicalCheck] using h)
    subst q
    exact .nonhalt hroot hsupport hno safe
  | split n s kids ih =>
    have hv : zipQueryOK B p n s = true ∧
        allMoves (fun mv => if mv.next.val ≤ cut then canonicalCheck B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true) = true := by
      simpa only [canonicalCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      have hslot : s.1.val < cut := by
        rw [← hs]
        exact knownRun_support p cut hcut hsupport n c hr
      refine .expand hroot hsupport hcut hno hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p s n B hw) ?_ ?_
      · intro mv hlt
        have hc := allMoves_sound _ hv.2 mv
        have hchild : canonicalCheck B (refine p s (some mv)) cut (kids mv) = true := by
          simpa [nextCut,hlt,Nat.le_of_lt hlt] using hc
        have hr' := refine_preserves_firstOne p s (some mv) hhole hroot
        have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
        have hs' := refine_support p s mv cut cut hsupport (Nat.le_refl _) hslot hlt
        simpa only [hs] using ih mv (refine p s (some mv)) cut hr' hn' hs' hcut hchild
      · intro q hq w r
        let mv : Move := ⟨w,r,q⟩
        have hlt : ¬ mv.next.val < cut := by simp [mv,hq]
        have hle : mv.next.val ≤ cut := by simp [mv,hq]
        have hc := allMoves_sound _ hv.2 mv
        have hchild : canonicalCheck B (refine p s (some mv)) (cut+1) (kids mv) = true := by
          simpa [nextCut,hlt,hle] using hc
        have hr' := refine_preserves_firstOne p s (some mv) hhole hroot
        have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
        have hs' := refine_support p s mv cut (cut+1) hsupport (by omega) (by omega) (by simpa [mv,hq])
        simpa only [hs,mv] using ih mv (refine p s (some mv)) (cut+1) hr' hn' hs' (by omega) hchild

theorem canonicalSplitChecked {B : Nat} {p : PartialMachine} {cut n : Nat} {s : Slot}
    {kids : Move → Audit} (hq : zipQueryOK B p n s = true)
    (h : ∀ mv, mv.next.val ≤ cut → canonicalCheck B (refine p s (some mv)) (nextCut cut mv) (kids mv) = true) :
    canonicalCheck B p cut (.split n s kids) = true := by
  change (zipQueryOK B p n s && allMoves (fun mv => if mv.next.val ≤ cut then canonicalCheck B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨hq, allMoves_of _ ?_⟩
  intro mv
  split
  · rename_i hh
    exact h mv hh
  · rfl

#print axioms canonicalSplitChecked
#print axioms certifiedCanonical
end BB6.Agent10CanonicalAudit
