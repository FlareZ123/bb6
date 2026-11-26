import Raw122Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122ResidualCompose
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def Covered (C : Nat) (p : PartialMachine) : Prop :=
  ∀ m : Machine, compatible p m → WeightedBound C m

def Good (C : Nat) (p : PartialMachine) (a : PartialAudit) : Prop :=
  ∀ e ∈ partialResiduals p a, Covered C e.2

theorem good_closed (C : Nat) (p : PartialMachine) (a : Audit) : Good C p (.closed a) := by
  intro e he
  rw [partialResiduals.eq_2] at he
  simp at he

theorem good_open {C : Nat} {p : PartialMachine} (h : Covered C p) : Good C p .unresolved := by
  intro e he
  rw [partialResiduals.eq_1] at he
  have hh : e = ([],p) := List.mem_singleton.mp he
  simpa only [hh] using h

theorem good_split {C : Nat} {p : PartialMachine} {n : Nat} {s : Slot} {kids : Move → PartialAudit}
    (h : ∀ mv, Good C (refine p s (some mv)) (kids mv)) : Good C p (.split n s kids) := by
  intro e he
  rw [partialResiduals.eq_3] at he
  obtain ⟨mv,_,hh⟩ := List.mem_flatMap.mp he
  obtain ⟨e',he',heq⟩ := List.mem_map.mp hh
  rw [← heq]
  exact h mv e' he'

theorem good_roster {C : Nat} {p : PartialMachine} {a : PartialAudit} {ps : List PartialMachine}
    (hroster : (partialResiduals p a).map Prod.snd = ps)
    (hc : ∀ p' ∈ ps, Covered C p') : Good C p a := by
  intro e he
  apply hc
  rw [← hroster]
  exact List.mem_map.mpr ⟨e,he,rfl⟩

theorem cover_of_good {C B : Nat} {p : PartialMachine} {a : PartialAudit}
    (hCB : B ≤ C) (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (hc : partialCheck B p a = true)
    (hg : Good C p a) : Covered C p := by
  intro m hm
  rcases partialSound B p a hf hno hc m hm with h|⟨e,he,hh⟩
  · intro k d hk hd
    exact Nat.le_trans (h k d hk hd) hCB
  · exact hg e he m hh

theorem never_bound {C : Nat} {p : PartialMachine}
    (h : ∀ m, compatible p m → NeverHalts m) : Covered C p := by
  intro m hm k d hk hd
  have hn := h m hm (k+1)
  unfold HaltsAfter at hk
  rw [hk.2] at hn
  contradiction

#print axioms cover_of_good
#print axioms never_bound
end BB6.Agent43Raw122ResidualCompose
