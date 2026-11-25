import CanonicalFrontier

namespace BB6.Agent47CanonicalRefinement
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
abbrev Entry := List Move × PartialMachine

def graftEntry (p : PartialMachine) (replacement : List Entry) (e : Entry) : List Entry :=
  if sameTable e.2 p then replacement.map (fun r => (e.1 ++ r.1,r.2)) else [e]

def graftRoster (p : PartialMachine) (replacement roster : List Entry) : List Entry :=
  roster.flatMap (graftEntry p replacement)

/-- Transfer a physical refinement to its entire root-fixing orbit. -/
theorem graftRoster_sound {B : Nat} {root p : PartialMachine}
    {replacement roster : List Entry}
    (hp : p initialSlot = some (some ⟨true,true,1⟩))
    (hroot : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hlocal : ∀ m, compatible p m → WeightedBound B m ∨
      ∃ r ∈ replacement, compatible r.2 m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ graftRoster p replacement roster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hroot m hm with hb | ⟨e,he,perm,hfix,hcomp⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 p = true
    · have heq := sameTable_sound hmatch
      have hc : compatible p (renameTable perm m) := heq ▸ hcomp
      rcases hlocal _ hc with hb | ⟨r,hr,hrc⟩
      · have hz := firstOne_terminal p hp _ hc
        exact Or.inl (weighted_rename_back B perm m hfix
          ((zeroNext_none_rename_iff perm m hfix).mp hz) hb)
      · refine Or.inr ⟨(e.1 ++ r.1,r.2), List.mem_flatMap.mpr ⟨e,he,?_⟩,
          perm,hfix,hrc⟩
        simp only [graftEntry, hmatch, ite_true]
        exact List.mem_map.mpr ⟨r,hr,rfl⟩
    · exact Or.inr ⟨e, List.mem_flatMap.mpr ⟨e,he,by simp [graftEntry,hmatch]⟩,
        perm,hfix,hcomp⟩

#print axioms graftRoster_sound
end BB6.Agent47CanonicalRefinement
