import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10ZipAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit

def zipQueryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (zipRead p n = some s) && (decide (p s = none) && weightOK p s n B)

theorem zipQueryOK_sound {B p n s} (h : zipQueryOK B p n s = true) :
    (knownRun p n).map readSlot = some s ∧ p s = none ∧ weightOK p s n B = true := by
  apply queryOK_sound
  simpa only [zipQueryOK,zipRead_eq,queryOK] using h

def zipCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => zipQueryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && zipCycle p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => zipQueryOK B p n s &&
      allMoves (fun mv => zipCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

noncomputable def certifiedZip (B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : zipCheck B p t = true) : WeightedTNFCertificate B p 6 := by
  induction t generalizing p with
  | last n s =>
    have hv : zipQueryOK B p n s = true ∧ restOK p s = true := by
      simpa only [zipCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      exact .lastHole hroot (support6 p) (by decide) hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using restOK_sound p s hv.2)
        (by simpa [hs] using weightOK_sound p s n B hw)
  | cycle e k r b =>
    have hv : 0 < k ∧ zipCycle p e k r b = true := by
      simpa only [zipCheck, Bool.and_eq_true, decide_eq_true_eq] using h
    exact .nonhalt hroot (support6 p) hno (zipCycle_sound p e k r b hv.1 hv.2)
  | far rev d C =>
    exact .nonhalt hroot (support6 p) hno (farSound p rev C (by simpa only [zipCheck] using h))
  | proven q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [zipCheck] using h)
    subst q
    exact .nonhalt hroot (support6 p) hno safe
  | split n s kids ih =>
    have hv : zipQueryOK B p n s = true ∧
        allMoves (fun mv => zipCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [zipCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
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


#print axioms certifiedZip
end BB6.Agent10ZipAudit
