import PackedPrefixAudit
import WeightedTNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
Two-bound hybrid certificate for a finite TNF query tree with a few
astronomical terminating leaves.

Every finite-checker node is evaluated at a *small* bound L, independently
of any enormous final score B. Exceptional leaves carry source proofs at B.
The only coupling is the mathematical inequality L ≤ B. This avoids
unfolding B in every finite `packedQueryOK` and `packedPrefixCheck`.
This module is reusable for the E1=0RD/D0=1LF parent with 4,873 finite
classified leaves and two exceptional one-hole tables (2265, 3506).
No parent proof is claimed by this checker in isolation.
-/

namespace BB6.Agent3TwoBoundAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedAudit BB6.Agent48PackedPrefix
open BB6Coverage.Agent13PackedZipper BB6.Agent3PackedCycle

inductive TwoBoundAudit (L B : Nat) : Type where
  | ordinary (t : Audit)
  | bounded (p : PartialMachine) (safe : ∀ m, compatible p m → WeightedBound B m)
  | split (n : Nat) (s : Slot) (kids : Move → TwoBoundAudit L B)

/-- A compact 24-child representation in the canonical Boolean/direction/state
    order used by allMoves. Invalid indices are structurally impossible. -/
def byTwoBoundMove {L B : Nat} (xs : List (TwoBoundAudit L B))
    (mv : Move) : TwoBoundAudit L B :=
  xs[12 * mv.write.toNat + 6 * mv.right.toNat + mv.next.val]?.getD
    (.ordinary (.last 0 (0,false)))

def check (L B : Nat) (p : PartialMachine) : TwoBoundAudit L B → Bool
  | .ordinary t => packedPrefixCheck L p t
  | .bounded q _ => tableOK p q
  | .split n s kids => packedQueryOK L p n s &&
      allMoves (fun mv => check L B (refine p s (some mv)) (kids mv))
termination_by structural t => t

/-- Prefix-cached checker: finite query nodes reuse the prior compressed
    physical tape/head, while large B is never evaluated by the checker. -/
def checkAt (L B : Nat) (p : PartialMachine) (t : Nat) (z : H) :
    TwoBoundAudit L B → Bool
  | .ordinary a => checkAtH L p t z a
  | .bounded q _ => tableOK p q
  | .split n s kids => match advanceH p t z n with
    | none => false
    | some c => queryAtH L p n s c &&
        allMoves (fun mv =>
          checkAt L B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem checkAt_eq (L B : Nat) (p : PartialMachine)
    (a : TwoBoundAudit L B) (t : Nat) (z : H)
    (h : runH p t startH = some z) :
    checkAt L B p t z a = check L B p a := by
  induction a generalizing p t z with
  | ordinary a =>
    simp only [checkAt,check,checkAtH_eq L p a t z h,
      packedPrefixCheck_eq]
  | bounded q safe => rfl
  | split n s kids ih =>
    rw [checkAt, check, advanceH_eq p t z h]
    cases hr : runH p n startH with
    | none => simp [queryFail L p n s hr]
    | some c =>
      simp only [queryAtH_eq L p n s c hr]
      by_cases hq : packedQueryOK L p n s = true
      · have hq' : queryAtH L p n s c = true :=
          (queryAtH_eq L p n s c hr).trans hq
        have hu := queryAtH_hole L p n s c hq'
        simp only [hq,Bool.true_and]
        apply congrArg allMoves
        funext mv
        exact ih mv (refine p s (some mv)) n c
          (refineRunH p s mv hu n startH c hr)
      · have hf : packedQueryOK L p n s = false :=
          Bool.eq_false_iff.mpr hq
        simp only [hf,Bool.false_and]

def checkPrefix (L B : Nat) (p : PartialMachine)
    (a : TwoBoundAudit L B) : Bool := checkAt L B p 0 startH a

theorem checkPrefix_eq (L B : Nat) (p : PartialMachine)
    (a : TwoBoundAudit L B) :
    checkPrefix L B p a = check L B p a :=
  checkAt_eq L B p a 0 startH rfl


/-- The same finite checker works regardless of the astronomical value B.
    Its semantic proof is a genuine original-machine weighted TNF tree, not
    an untrusted Boolean postulate. -/
noncomputable def certified (L B : Nat) (hLB : L ≤ B)
    (p : PartialMachine) (t : TwoBoundAudit L B)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : check L B p t = true) :
    WeightedTNFCertificate B p 6 := by
  induction t generalizing p with
  | ordinary a =>
    have hsmall : WeightedTNFCertificate L p 6 :=
      certifiedPacked L p a hroot hno
        (by simpa only [check,packedPrefixCheck_eq] using h)
    exact .weightedLeaf hroot (support6 p) hno
      (fun m hm k d hk hd =>
        Nat.le_trans (hsmall.sound m hm k d hk hd) hLB)
  | bounded q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [check] using h)
    subst q
    exact .weightedLeaf hroot (support6 p) hno safe
  | split n s kids ih =>
    have hv : packedQueryOK L p n s = true ∧
        allMoves (fun mv => check L B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [check, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := packedQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      have hSmall : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
          d + n + 1 ≤ L := by
        simpa only [hs] using weightOK_sound p s n L hw
      have hLarge : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
          d + n + 1 ≤ B := by
        intro d hd
        exact Nat.le_trans (hSmall d hd) hLB
      refine .expand hroot (support6 p) (by decide) hno hr
        (by simpa [hs] using hhole) hLarge ?_ ?_
      · intro mv _
        have hchild := allMoves_sound _ hv.2 mv
        have hr' := refine_preserves_firstOne p s (some mv) hhole hroot
        have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
        simpa only [hs] using ih mv (refine p s (some mv)) hr' hn' hchild
      · intro q hq _ _
        have hlt := q.isLt
        omega

theorem sound (L B : Nat) (hLB : L ≤ B)
    (p : PartialMachine) (t : TwoBoundAudit L B)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : check L B p t = true) :
    Cover (WeightedBound B) p :=
  (certified L B hLB p t hroot hno h).toCover

#print axioms checkPrefix_eq
#print axioms certified
#print axioms sound
end BB6.Agent3TwoBoundAudit
