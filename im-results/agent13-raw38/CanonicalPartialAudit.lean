import PartialAudit
import WeightedTNFQueueOrbit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13CanonicalPartialAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent50TNFPilot BB6.Agent8TNFPath BB6.Agent10ZipAudit BB6.Agent47PartialAudit

/-- Canonical addresses introduce only the least unused state label. -/
def canonicalAddress (cut : Nat) : List Move → Bool
  | [] => true
  | mv :: rest => decide (mv.next.val ≤ cut) &&
      canonicalAddress (max cut (mv.next.val+1)) rest

def canonicalResiduals (cut : Nat) (p : PartialMachine) (t : PartialAudit) :=
  (partialResiduals p t).filter fun e => canonicalAddress cut e.1

/-- A checked partial audit can omit every noncanonical child by marking
    it unresolved. Those leaves disappear from the canonical residual
    roster without requiring their individual semantic certificates. -/
theorem canonicalPartialSound (B cut : Nat) (p : PartialMachine) (t : PartialAudit)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : partialCheck B p t = true) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound B m ∨
      ∃ e ∈ canonicalResiduals cut p t, TNFQuotientCompatible e.2 m := by
  induction t generalizing p cut with
  | unresolved =>
    intro m hm
    exact Or.inr ⟨([],p), by simp [canonicalResiduals, partialResiduals, canonicalAddress], hm⟩
  | closed t =>
    intro m hm
    obtain ⟨perm, hp, hc⟩ := hm
    have hb := (certifiedZip B p t hf hno h).sound (renameTable perm m) hc
    have hz := firstOne_terminal p hf (renameTable perm m) hc
    exact Or.inl (weighted_rename_back B perm m hp ((zeroNext_none_rename_iff perm m hp).mp hz) hb)
  | split n s kids ih =>
    have hv : zipQueryOK B p n s = true ∧ allMoves
        (fun mv => partialCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [partialCheck, Bool.and_eq_true] using h
    obtain ⟨hread, hhole, hw⟩ := zipQueryOK_sound hv.1
    have hq : s.1.val < cut := by
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
        have he : readSlot c = s := by simpa [hr] using hread
        rw [← he]
        exact knownRun_support p cut hcut hs n c hr
    have hhalt : ∀ m, compatible (refine p s none) m → WeightedBound B m := by
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
        have he : readSlot c = s := by simpa [hr] using hread
        intro m hm
        exact first_hole_weighted_halt B p n c hf hr
          (by simpa [he] using hhole)
          (by simpa [he] using weightOK_sound p s n B hw) m
          (by simpa [he] using hm)
    intro m hm
    rcases tnf_branch_frontier B cut p s hcut hs hhole hq hf hhalt m hm with hb | ⟨mv,hcan,hc⟩
    · exact Or.inl hb
    · let cut' := max cut (mv.next.val+1)
      have hle : cut ≤ cut' := Nat.le_max_left _ _
      have hcut' : 0 < cut' := Nat.lt_of_lt_of_le hcut hle
      have hmv : mv.next.val < cut' := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
      have hs' := refine_support p s mv cut cut' hs hle (Nat.lt_of_lt_of_le hq hle) hmv
      have hf' := refine_preserves_firstOne p s (some mv) hhole hf
      have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
      rcases ih mv cut' (refine p s (some mv)) hcut' hs' hf' hn'
        (allMoves_sound _ hv.2 mv) m hc with hb | ⟨e,he,hc'⟩
      · exact Or.inl hb
      · have hm' := List.mem_filter.mp he
        have hmem : (mv :: e.1,e.2) ∈ partialResiduals p (.split n s kids) := by
          exact List.mem_flatMap.mpr ⟨mv, auditMoves_complete mv,
            List.mem_map.mpr ⟨e,hm'.1,rfl⟩⟩
        have hp' : canonicalAddress cut (mv :: e.1) = true := by
          simp only [canonicalAddress, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hcan, hm'.2⟩
        exact Or.inr ⟨(mv :: e.1,e.2), List.mem_filter.mpr ⟨hmem,hp'⟩, hc'⟩

theorem canonicalPartialCover (B cut : Nat) (p : PartialMachine) (t : PartialAudit)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : partialCheck B p t = true)
    (C : Nat) (hBC : B ≤ C)
    (hr : ∀ e ∈ canonicalResiduals cut p t, Cover (WeightedBound C) e.2) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound C m := by
  intro m hm
  rcases canonicalPartialSound B cut p t hcut hs hf hno h m hm with hb | ⟨e,he,perm,hp,hc⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hBC
  · have hb := (hr e he).sound (renameTable perm m) hc
    obtain ⟨perm0, hp0, hc0⟩ := hm
    have hz0 := firstOne_terminal p hf (renameTable perm0 m) hc0
    exact weighted_rename_back C perm m hp ((zeroNext_none_rename_iff perm0 m hp0).mp hz0) hb

#print axioms canonicalPartialSound
#print axioms canonicalPartialCover
end BB6.Agent13CanonicalPartialAudit
