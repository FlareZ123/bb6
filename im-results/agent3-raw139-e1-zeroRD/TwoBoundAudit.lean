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

def check (L B : Nat) (p : PartialMachine) : TwoBoundAudit L B → Bool
  | .ordinary t => packedPrefixCheck L p t
  | .bounded q _ => tableOK p q
  | .split n s kids => packedQueryOK L p n s &&
      allMoves (fun mv => check L B (refine p s (some mv)) (kids mv))
termination_by structural t => t

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

#print axioms certified
#print axioms sound
end BB6.Agent3TwoBoundAudit
