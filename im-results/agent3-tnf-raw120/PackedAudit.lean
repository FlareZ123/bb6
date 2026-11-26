import PackedCycle
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3PackedAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedCycle BB6Coverage.Agent13PackedZipper

def packedQueryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (readRunP p n = some s) && (decide (p s = none) && weightOK p s n B)

theorem packedQueryOK_sound {B p n s} (h : packedQueryOK B p n s = true) :
    (knownRun p n).map readSlot = some s ∧ p s = none ∧ weightOK p s n B = true := by
  apply queryOK_sound
  simpa only [packedQueryOK,readRunP_eq,zipRead_eq,queryOK] using h

def packedCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => packedQueryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleH p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => packedQueryOK B p n s &&
      allMoves (fun mv => packedCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

noncomputable def certifiedPacked (B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : packedCheck B p t = true) : WeightedTNFCertificate B p 6 := by
  induction t generalizing p with
  | last n s =>
    have hv : packedQueryOK B p n s = true ∧ restOK p s = true := by
      simpa only [packedCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := packedQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      exact .lastHole hroot (support6 p) (by decide) hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using restOK_sound p s hv.2)
        (by simpa [hs] using weightOK_sound p s n B hw)
  | cycle e k r b =>
    have hv : 0 < k ∧ cycleH p e k r b = true := by
      simpa only [packedCheck, Bool.and_eq_true, decide_eq_true_eq] using h
    exact .nonhalt hroot (support6 p) hno (cycleH_sound p e k r b hv.1 hv.2)
  | far rev d C =>
    exact .nonhalt hroot (support6 p) hno (farSound p rev C (by simpa only [packedCheck] using h))
  | proven q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [packedCheck] using h)
    subst q
    exact .nonhalt hroot (support6 p) hno safe
  | split n s kids ih =>
    have hv : packedQueryOK B p n s = true ∧
        allMoves (fun mv => packedCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [packedCheck, Bool.and_eq_true] using h
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


#print axioms certifiedPacked
end BB6.Agent3PackedAudit
