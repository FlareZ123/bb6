import TNFGraph
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6NormalizedPrefix
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit BB6.Agent48PrefixAudit BB6Coverage.Agent31Pump
open BB6.Agent10ZipAudit BB6.Agent6TNFGraph

inductive Tree (B : Nat) where
  | closed (a : Audit)
  | graph (n mask : Nat)
  | covered (p : PartialMachine) (h : Cover (WeightedBound B) p)
  | split (n : Nat) (s : Slot) (kids : Move → Tree B)

def checkAt (B : Nat) (p : PartialMachine) (cut t : Nat) (z : Z) : Tree B → Bool
  | .closed a => BB6.Agent48PrefixAudit.checkAt B p t z a
  | .graph n mask => match advance p t z n with
    | none => false
    | some c => mask.testBit c.q.val && graphOK p mask
  | .covered q _ => tableOK p q
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => queryAt B p n s c && allMoves (fun mv =>
        if mv.next.val ≤ cut then checkAt B (refine p s (some mv))
          (max cut (mv.next.val+1)) n c (kids mv) else true)
termination_by structural a => a

theorem soundAt (B : Nat) (p : PartialMachine) (tree : Tree B) (cut t : Nat) (z : Z)
    (hs : TNFSupport p cut) (hcut : 0 < cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p) (hr : zrun p t start = some z)
    (h : checkAt B p cut t z tree = true) : Cover (WeightedBound B) p := by
  induction tree generalizing p cut t z with
  | closed a =>
    have h' : zipCheck B p a = true := by
      rw [← BB6.Agent48PrefixAudit.checkAt_eq B p a t z hr]
      exact h
    exact .leaf p (certifiedZip B p a hf hn h').sound
  | graph n mask =>
    rw [checkAt,advance_eq p t z hr] at h
    cases hc : zrun p n start with
    | none => simp [hc] at h
    | some c =>
      have hg : mask.testBit c.q.val = true ∧ graphOK p mask = true := by
        simpa only [hc,Bool.and_eq_true] using h
      have hknown : knownRun p n = some (embed c) := by rw [knownRun_zip,hc]; rfl
      have hmem : mask.testBit (embed c).state.val = true := hg.1
      exact .leaf p (fun m hm => weighted_never B m
        (weightedTNFKnownRunForever_sound p (graphForever p mask n _ hknown hmem hg.2) m hm))
  | covered q safe =>
    have he : p = q := tableOK_sound p q h
    subst q; exact safe
  | split n s kids ih =>
    rw [checkAt,advance_eq p t z hr] at h
    cases hc : zrun p n start with
    | none => simp [hc] at h
    | some c =>
      have hv : queryAt B p n s c = true ∧ allMoves (fun mv =>
        if mv.next.val ≤ cut then checkAt B (refine p s (some mv))
          (max cut (mv.next.val+1)) n c (kids mv) else true) = true := by
        simpa only [hc,Bool.and_eq_true] using h
      have hquery := (queryAt_eq B p n s c hc).symm.trans hv.1
      obtain ⟨hread,hu,hw⟩ := zipQueryOK_sound hquery
      have hk : knownRun p n = some (embed c) := by rw [knownRun_zip,hc]; rfl
      have hslot : readSlot (embed c) = s := by simpa [hk] using hread
      have hslotcut : s.1.val < cut := by
        rw [← hslot]
        exact knownRun_support p cut hcut hs n _ hk
      have childSound : ∀ mv : Move, mv.next.val ≤ cut → Cover (WeightedBound B) (refine p s (some mv)) := by
        intro mv hm
        have hcheck := allMoves_sound _ hv.2 mv
        simp only [hm,ite_true] at hcheck
        exact ih mv _ _ n c
          (refine_support p s mv cut _ hs (Nat.le_max_left _ _)
            (Nat.lt_of_lt_of_le hslotcut (Nat.le_max_left _ _))
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)))
          (Nat.lt_of_lt_of_le hcut (Nat.le_max_left _ _))
          (refine_preserves_firstOne p s (some mv) hu hf)
          (weightedTNFNoAssignedHalt_refine p s mv hn)
          (refineRun p s mv hu n start c hc) hcheck
      apply first_hole_tnf_cover B cut p n (embed c) hcut hs hf hk
      · simpa only [hslot] using hu
      · simpa only [hslot] using weightOK_sound p s n B hw
      · intro mv hm m hcompat
        rw [hslot] at hcompat
        exact (childSound mv (Nat.le_of_lt hm)).sound m hcompat
      · intro q hq w r m hcompat
        rw [hslot] at hcompat
        exact (childSound ⟨w,r,q⟩ (Nat.le_of_eq hq)).sound m hcompat

def check (B : Nat) (p : PartialMachine) (cut : Nat) (tree : Tree B) : Bool :=
  checkAt B p cut 0 start tree

theorem sound (B : Nat) (p : PartialMachine) (cut : Nat) (tree : Tree B)
    (hs : TNFSupport p cut) (hcut : 0 < cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p) (h : check B p cut tree = true) : Cover (WeightedBound B) p :=
  soundAt B p tree cut 0 start hs hcut hf hn rfl h

#print axioms sound
end BB6.Agent6NormalizedPrefix
