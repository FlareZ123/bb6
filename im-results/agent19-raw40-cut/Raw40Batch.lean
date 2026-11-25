import Raw40RDLCRefine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

def batchRemaining (ps : List PartialMachine) := rdlcRemaining.filter fun e => !(ps.any (sameTable e.2))

theorem batch_local_sound (ps : List PartialMachine)
    (hs : ∀ p ∈ ps, ∀ m, TNFQuotientCompatible p m → WeightedBound 7014 m) :
    ∀ m, TNFQuotientCompatible parent m → WeightedBound 7014 m ∨
    ∃ e ∈ batchRemaining ps, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases rdlc_local_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hh : ps.any (sameTable e.2) = true
    · obtain ⟨p,hp,heq⟩ := List.any_eq_true.mp hh
      have eq := sameTable_sound heq
      exact Or.inl (hs p hp m (eq ▸ hq))
    · exact Or.inr ⟨e,by simp [batchRemaining,he,hh],hq⟩

noncomputable def batchRoster (ps : List PartialMachine) := graftRoster parent (batchRemaining ps) BB6.Agent47CanonicalRaw114Accepted.roster

theorem batch_roster_sound (ps : List PartialMachine)
    (hs : ∀ p ∈ ps, ∀ m, TNFQuotientCompatible p m → WeightedBound 7014 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ batchRoster ps, TNFQuotientCompatible e.2 m :=
  quotient_graft_sound BB6.Agent47CanonicalRaw114Accepted.sound (batch_local_sound ps hs)

#print axioms batch_roster_sound
end BB6.Agent19Raw40
