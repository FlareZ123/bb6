import Raw47AfterRaw112Conditional
import Raw140ThreeHoleCut
import QuotientRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Replace the unique Raw140 parent inside the post-Raw47 Canonical37 roster by
the exact twelve source-checked Raw140 residual cylinders.  This keeps the
residuals as first-class global obligations rather than requiring twelve Covers
up front.
-/

namespace BB6.Agent15Raw140Canonical48

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent50QuotientRefinement
open BB6ChampionArithmetic

abbrev p47 : PartialMachine :=
  BB6.Agent9Raw47AfterRaw112Conditional.p47

noncomputable abbrev baseRoster :=
  BB6.Agent9Raw47AfterRaw112Conditional.roster37

abbrev p140 : PartialMachine :=
  BB6.Agent10Raw140ThreeHole.parent

theorem p140_count37 :
    (baseRoster.filter (fun e => sameTable e.2 p140)).length = 1 := by
  decide

theorem base_sound_at (B : Nat) (hFloor : 6766859 ≤ B)
    (h47 : Cover (WeightedBound 6766859) p47) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ baseRoster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent9Raw47AfterRaw112Conditional.conditional_sound h47 m hm with
    hsmall | hrest
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

def raw140RefinementAt (B : Nat) (hCut : 10010 ≤ B) :
    Refinement B where
  parent := p140
  children := BB6.Agent10Raw140ThreeHole.remaining
  sound := by
    intro m hm
    rcases BB6.Agent10Raw140ThreeHole.quotient_sound m hm with hb | hr
    · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) hCut)
    · exact Or.inr hr

def raw140Shape : Refinement 10010 :=
  raw140RefinementAt 10010 (by omega)

noncomputable def roster48 :=
  refineRoster [raw140Shape] baseRoster

theorem count48 : roster48.length = 48 := by
  decide

theorem raw140_parent_removed :
    (roster48.filter (fun e => sameTable e.2 p140)).length = 0 := by
  decide

theorem roster_shape_at (B : Nat) (hCut : 10010 ≤ B) :
    refineRoster [raw140RefinementAt B hCut] baseRoster = roster48 := by
  rfl

theorem refined_sound_at (B : Nat) (hFloor : 6766859 ≤ B)
    (hCut : 10010 ≤ B)
    (h47 : Cover (WeightedBound 6766859) p47) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster48, TNFQuotientCompatible e.2 m := by
  intro m hm
  have hbase := base_sound_at B hFloor h47 m hm
  have href := refineRoster_sound [raw140RefinementAt B hCut] baseRoster m hbase
  rw [roster_shape_at B hCut] at href
  exact href

theorem conditional_exact_at_champion_score
    (h47 : Cover (WeightedBound 6766859) p47)
    (hLeaves : ∀ e ∈ roster48,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) := by
  have hFloor :
      6766859 ≤ proposedTM63Moves + 7 :=
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
  have hCut : 10010 ≤ proposedTM63Moves + 7 := by omega
  exact exact_from_quotient_roster (by omega) hFloor
    (refined_sound_at (proposedTM63Moves + 7) hFloor hCut h47)
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p140_count37
#print axioms count48
#print axioms raw140_parent_removed
#print axioms roster_shape_at
#print axioms refined_sound_at
#print axioms conditional_exact_at_champion_score

end BB6.Agent15Raw140Canonical48
