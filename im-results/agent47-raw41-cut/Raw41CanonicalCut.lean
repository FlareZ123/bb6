import Raw41TwoCut
import CanonicalPartial
import CanonicalRaw114Accepted

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent19CanonicalPartial BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster

/-- A fully checked ordinary tree can be canonicalized without repeating its
certificate checks. The canonical checker visits only a subset of children. -/
theorem canonical_of_partial (B : Nat) (p : PartialMachine) (cut : Nat) (t : PartialAudit)
    (h : partialCheck B p t = true) : canonicalCheck B p cut t = true := by
  induction t generalizing p cut with
  | unresolved => rfl
  | closed a => simpa only [canonicalCheck, prefixCheck_eq, partialCheck] using h
  | split n s kids ih =>
    have h' : zipQueryOK B p n s = true ∧ allMoves (fun mv => partialCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [partialCheck, Bool.and_eq_true] using h
    simp only [canonicalCheck,h'.1,Bool.true_and]
    apply allMoves_of
    intro mv
    by_cases hv : mv.next.val ≤ cut
    · simp only [if_pos hv]
      exact ih mv _ _ (allMoves_sound _ h'.2 mv)
    · simp [hv]

def canonicalRemaining := canonicalResiduals parent 4 tree

theorem supported : TNFSupport parent 4 := supportOK_sound _ _ (by decide)
theorem canonical_checked : canonicalCheck 16 parent 4 tree = true := canonical_of_partial _ _ _ _ checked
theorem canonical_count : canonicalRemaining.length = 153 := by decide +kernel

theorem canonical_sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound 16 m ∨ ∃ e ∈ canonicalRemaining, TNFQuotientCompatible e.2 m :=
  canonicalSound _ _ _ _ (by decide) supported parent_root parent_nohalt canonical_checked

noncomputable def roster := graftRoster parent canonicalRemaining BB6.Agent47CanonicalRaw114Accepted.roster

theorem parent_count : (BB6.Agent47CanonicalRaw114Accepted.roster.filter (fun e => sameTable e.2 parent)).length = 1 := by decide +kernel
theorem roster_count : roster.length = 229 := by decide +kernel
theorem roster_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent47CanonicalRaw114Accepted.sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases ht : sameTable e.2 parent = true
    · have eq : e.2 = parent := sameTable_sound ht
      rcases canonical_sound m (eq ▸ hq) with hb | ⟨e',he',hq'⟩
      · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
      · refine Or.inr ⟨(e.1 ++ e'.1,e'.2),?_,hq'⟩
        apply List.mem_flatMap.mpr
        exact ⟨e,he,by simp only [graftEntry,ht,if_true]; exact List.mem_map.mpr ⟨e',he',rfl⟩⟩
    · exact Or.inr ⟨e,List.mem_flatMap.mpr ⟨e,he,by simp [graftEntry,ht]⟩,hq⟩

#print axioms canonical_of_partial
#print axioms canonical_count
#print axioms canonical_sound
#print axioms parent_count
#print axioms roster_count
#print axioms roster_sound
end BB6.Agent47Raw41
