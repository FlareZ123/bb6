import FourHoleResidualRoster
import WeightedTNFQueueOrbit
import WeightedFirstOneCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47CanonicalFrontier
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster

/-- State-introduction canonicality, starting with cut introduced states. -/
def canonicalAddress (cut : Nat) : List Move → Bool
  | [] => true
  | mv :: xs => decide (mv.next.val ≤ cut) &&
      canonicalAddress (max cut (mv.next.val + 1)) xs

theorem quotientSafe {p : PartialMachine} {B : Nat}
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hs : ∀ m, compatible p m → WeightedBound B m)
    (m : Machine) (hq : TNFQuotientCompatible p m) : WeightedBound B m := by
  rcases hq with ⟨e, he, hm⟩
  have hz := firstOne_terminal p hf (renameTable e m) hm
  exact weighted_rename_back B e m he ((zeroNext_none_rename_iff e m he).mp hz)
    (hs _ hm)

/-- Normalize only at an actual first hole, preserve earlier assignments,
    and keep composing the state permutations. This does not require the raw
    residual set to be closed under state renaming. -/
theorem quotientFrontier_sound {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) (cut : Nat) (hcut : 0 < cut)
    (hs : TNFSupport p cut) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound B m ∨
      ∃ address q, OpenLeaf f address q ∧ canonicalAddress cut address = true ∧
        TNFQuotientCompatible q m := by
  induction f generalizing cut with
  | residual path =>
      intro m hm
      exact Or.inr ⟨[], _, OpenLeaf.here path, rfl, hm⟩
  | closed path cert =>
      intro m hm
      exact Or.inl (quotientSafe (RawRootPath.rootRow path) cert.sound m hm)
  | @expand p n c path hrun hhole hweight children ih =>
      intro m hm
      have hslot : (readSlot c).1.val < cut := knownRun_support p cut hcut hs n c hrun
      have hf := RawRootPath.rootRow path
      rcases tnf_branch_frontier B cut p (readSlot c) hcut hs hhole hslot hf
        (first_hole_weighted_halt B p n c hf hrun hhole hweight) m hm with hb | ⟨mv, hv, hq⟩
      · exact Or.inl hb
      · let cut' := max cut (mv.next.val + 1)
        have hle : cut ≤ cut' := Nat.le_max_left _ _
        have hcut' : 0 < cut' := Nat.lt_of_lt_of_le hcut hle
        have hv' : mv.next.val < cut' := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
        have hs' := refine_support p (readSlot c) mv cut cut' hs hle (Nat.lt_of_lt_of_le hslot hle) hv'
        rcases ih mv cut' hcut' hs' m hq with hb | ⟨address, q, hleaf, hcan, hq'⟩
        · exact Or.inl hb
        · exact Or.inr ⟨mv :: address, q,
            OpenLeaf.child path hrun hhole hweight children mv hleaf,
            by simpa [canonicalAddress, hv, cut'] using hcan, hq'⟩

def identityPerm : StatePerm := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

theorem identityRename (m : Machine) : renameTable identityPerm m = m := by
  funext slot
  rcases slot with ⟨q,b⟩
  cases h : m (q,b) with
  | none => simp [renameTable, identityPerm, h]
  | some mv => cases mv; simp [renameTable, identityPerm, renameMove, h]

theorem compatible_quotient {p : PartialMachine} {m : Machine}
    (hm : compatible p m) : TNFQuotientCompatible p m :=
  ⟨identityPerm, rfl, by rw [identityRename]; exact hm⟩

noncomputable def canonicalRemainingRoster : List (List Move × PartialMachine) :=
  remainingRootRoster.filter fun e => canonicalAddress 2 e.1

/-- Exact source frontier modulo state-introduction renaming. The original
    37 checked witness leaves are still discharged, and only canonical
    residual addresses remain. -/
theorem canonicalRemaining_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨
      ∃ e ∈ canonicalRemainingRoster, TNFQuotientCompatible e.2 m := by
  have hscope : TNFSupport BB6.Agent50TNFPilot.root 2 := by
    simpa [BB6.Agent50TNFPilot.root] using firstOneCylinder_tnf_support
  rcases quotientFrontier_sound rootFrontier 2 (by decide) hscope m
    (compatible_quotient hm) with hb | ⟨address, q, hleaf, hcan, hq⟩
  · exact Or.inl hb
  · have hmem : (address, q) ∈ residuals rootFrontier :=
      OpenLeaf.mem_residuals hleaf
    cases hw : residualHasWitness q with
    | true =>
        have hf : q initialSlot = some (some ⟨true,true,1⟩) :=
          OpenLeaf.extends hleaf initialSlot _ rfl
        exact Or.inl (quotientSafe hf (residualHasWitness_sound q hw) m hq)
    | false =>
        have hr : (address, q) ∈ remainingRootRoster :=
          List.mem_filter.mpr ⟨hmem, by simp [hw]⟩
        exact Or.inr ⟨(address,q), List.mem_filter.mpr ⟨hr,hcan⟩,hq⟩

theorem canonicalRemaining_count : canonicalRemainingRoster.length = 96 := by
  decide

/-- Mixed-bound quotient composition. Only canonical representatives need
    B-bound Covers; the C-bound branch is lifted monotonically. A residual
    is interpreted modulo a root-fixing permutation, not as a raw match. -/
theorem cover_of_quotient_roster {C B : Nat} (hCB : C ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hroot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hleaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder := by
  refine Cover.leaf _ ?_
  intro m hm
  have hmr : compatible BB6.Agent50TNFPilot.root m := by
    simpa [BB6.Agent50TNFPilot.root] using hm
  rcases hroot m hmr with hb | ⟨entry, he, e, he0, hc⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hCB
  · have hz := firstOne_terminal _ firstOneCylinder_root_action m hm
    exact weighted_rename_back B e m he0 hz ((hleaves entry he).sound _ hc)

theorem exact_from_quotient_roster {C B : Nat} (hB : 6 ≤ B) (hCB : C ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hroot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hleaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_weighted_first_one B hB (cover_of_quotient_roster hCB hroot hleaves) champ

#print axioms quotientFrontier_sound
#print axioms canonicalRemaining_sound
#print axioms canonicalRemaining_count
#print axioms cover_of_quotient_roster
#print axioms exact_from_quotient_roster

end BB6.Agent47CanonicalFrontier
