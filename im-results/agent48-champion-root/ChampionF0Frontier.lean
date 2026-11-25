import F0SiblingIntegration
import Champion0RACover
import ChampionRemainingCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent48F0Frontier

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster BB6.Agent13MixedBound109
open BB6.Agent6F0 BB6.Agent6F0.AFirst

def parentRA := BB6.Agent6F0.parent ⟨false,true,0⟩
def parentRC := BB6.Agent6F0.parent ⟨false,true,2⟩
def parentRE := BB6.Agent6F0.parent ⟨true,true,4⟩
def hardRC := childA ⟨false,true,2⟩ ⟨false,true,3⟩
def hardRE := child ⟨true,true,4⟩ ⟨false,true,3⟩

def replaced (p : PartialMachine) : Bool :=
  sameTable p parentRA || sameTable p parentRC || sameTable p parentRE

noncomputable def earlierResiduals : List (List Move × PartialMachine) :=
  BB6.Agent6F0.Integration.remaining.filter (fun e => !replaced e.2)

/-- Exact-table filtering removes three two-hole cylinders. RA is closed;
    RC and RE are replaced by one one-hole obligation each. -/
theorem earlier_count : earlierResiduals.length = 110 := by decide

noncomputable def obligations : List PartialMachine :=
  hardRC :: hardRE :: earlierResiduals.map Prod.snd

theorem obligation_count : obligations.length = 112 := by
  simp [obligations, earlier_count]

theorem cover_replaced (B : Nat) (hB : 49394 ≤ B)
    (hRC : Cover (WeightedBound B) hardRC)
    (hRE : Cover (WeightedBound B) hardRE)
    (p : PartialMachine) (hp : replaced p = true) :
    Cover (WeightedBound B) p := by
  unfold replaced at hp
  simp only [Bool.or_eq_true] at hp
  rcases hp with (hRA | hRC') | hRE'
  · rw [sameTable_sound hRA]
    exact BB6.Agent48RA.cover_zeroRA B (by omega)
  · rw [sameTable_sound hRC']
    exact BB6.Agent48Remaining.cover_zeroRC_of_RD B (by omega) hRC
  · rw [sameTable_sound hRE']
    exact BB6.Agent48Remaining.cover_oneRE_of_RD B (by omega) hRE

theorem covers_old_remaining
    (h : ∀ p ∈ obligations, Cover (WeightedBound championScore) p) :
    ∀ e ∈ BB6.Agent6F0.Integration.remaining,
      Cover (WeightedBound championScore) e.2 := by
  intro e he
  cases hp : replaced e.2 with
  | true =>
      apply cover_replaced championScore
        BB6.Agent6F0.Integration.champion_score_ge_49394
        (h hardRC (by simp [obligations]))
        (h hardRE (by simp [obligations])) e.2 hp
  | false =>
      apply h e.2
      unfold obligations
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      exact ⟨e, List.mem_filter.mpr ⟨he,by simp [hp]⟩,rfl⟩

theorem raw139_cover
    (h : ∀ p ∈ obligations, Cover (WeightedBound championScore) p) :
    Cover (WeightedBound championScore) championResidual :=
  BB6.Agent6F0.Integration.residual_cover (covers_old_remaining h)

theorem exact_from_obligations
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (h : ∀ p ∈ obligations, Cover (WeightedBound championScore) p) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent6F0.Integration.exact_from_remaining hOther (covers_old_remaining h)

theorem refined_obligation_count :
    (BB6.Agent47Canonical78.roster.filter
      (fun e => e.1 ≠ championResidualAddress)).length +
      obligations.length = 189 := by
  rw [canonical78_other_address_count,obligation_count]

#print axioms earlier_count
#print axioms obligation_count
#print axioms raw139_cover
#print axioms exact_from_obligations
#print axioms refined_obligation_count

end BB6.Agent48F0Frontier
