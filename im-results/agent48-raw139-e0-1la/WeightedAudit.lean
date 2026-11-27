import PackedPrefixAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48WeightedAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedAudit BB6.Agent48PackedPrefix
open BB6Coverage.Agent13PackedZipper BB6.Agent3PackedCycle

inductive WeightedAudit (B : Nat) : Type
  | ordinary (t : Audit)
  | bounded (p : PartialMachine) (safe : ∀ m, compatible p m → WeightedBound B m)
  | split (n : Nat) (s : Slot) (kids : Move → WeightedAudit B)

def byWeightedMove {B : Nat} (xs : List (WeightedAudit B)) (mv : Move) : WeightedAudit B :=
  xs[12 * mv.write.toNat + 6 * mv.right.toNat + mv.next.val]?.getD (.ordinary (.last 0 (0,false)))

def check (B : Nat) (p : PartialMachine) : WeightedAudit B → Bool
  | .ordinary t => packedPrefixCheck B p t
  | .bounded q _ => tableOK p q
  | .split n s kids => packedQueryOK B p n s &&
      allMoves (fun mv => check B (refine p s (some mv)) (kids mv))
termination_by structural t => t


def checkAt (B : Nat) (p : PartialMachine) (t : Nat) (z : H) : WeightedAudit B → Bool
  | .ordinary a => checkAtH B p t z a
  | .bounded q _ => tableOK p q
  | .split n s kids => match advanceH p t z n with
    | none => false
    | some c => queryAtH B p n s c &&
        allMoves (fun mv => checkAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem checkAt_eq (B : Nat) (p : PartialMachine) (a : WeightedAudit B)
    (t : Nat) (z : H) (h : runH p t startH = some z) :
    checkAt B p t z a = check B p a := by
  induction a generalizing p t z with
  | ordinary a => simp only [checkAt,check,checkAtH_eq B p a t z h,packedPrefixCheck_eq]
  | bounded q safe => rfl
  | split n s kids ih =>
    rw [checkAt,check,advanceH_eq p t z h]
    cases hr : runH p n startH with
    | none => simp [queryFail B p n s hr]
    | some c =>
      simp only [queryAtH_eq B p n s c hr]
      by_cases hq : packedQueryOK B p n s = true
      · have hq' : queryAtH B p n s c = true := (queryAtH_eq B p n s c hr).trans hq
        have hu := queryAtH_hole B p n s c hq'
        simp only [hq,Bool.true_and]
        apply congrArg allMoves
        funext mv
        exact ih mv (refine p s (some mv)) n c (refineRunH p s mv hu n startH c hr)
      · have hf : packedQueryOK B p n s = false := Bool.eq_false_iff.mpr hq
        simp only [hf,Bool.false_and]

def checkPrefix (B : Nat) (p : PartialMachine) (a : WeightedAudit B) : Bool :=
  checkAt B p 0 startH a

theorem checkPrefix_eq (B : Nat) (p : PartialMachine) (a : WeightedAudit B) :
    checkPrefix B p a = check B p a := checkAt_eq B p a 0 startH rfl

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

#print axioms checkPrefix_eq
#print axioms certified
end BB6.Agent48WeightedAudit
