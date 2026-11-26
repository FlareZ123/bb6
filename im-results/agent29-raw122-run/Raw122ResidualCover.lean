import Raw122Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29ResidualCover
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def Cover (B : Nat) := { p : PartialMachine // ∀ m, compatible p m → WeightedBound B m }

theorem bound_mono {B C : Nat} {m : Machine} (h : B ≤ C) (hb : WeightedBound B m) : WeightedBound C m := by
  intro k d hk hd
  exact Nat.le_trans (hb k d hk hd) h

theorem never_bound {B : Nat} {m : Machine} (hn : NeverHalts m) : WeightedBound B m := by
  intro k d hk hd
  exfalso
  have h := hn (k+1)
  rw [hk.2] at h
  contradiction

def covered (C : Nat) (cs : List (Cover C)) (p : PartialMachine) : Bool := cs.any (fun q => tableOK p q.val)

theorem covered_sound {C : Nat} {cs : List (Cover C)} {p : PartialMachine} (h : covered C cs p = true) (m : Machine) (hm : compatible p m) : WeightedBound C m := by
  obtain ⟨q,_,hq⟩ := List.any_eq_true.mp h
  have he := tableOK_sound p q.val hq
  exact q.property m (he ▸ hm)

theorem cover_of_residuals {B C : Nat} {p : PartialMachine} {t : PartialAudit}
    (hBC : B ≤ C) (hf : p initialSlot = some (some ⟨true,true,1⟩)) (hno : weightedTNFNoAssignedHalt p)
    (ha : partialCheck B p t = true) (cs : List (Cover C))
    (hc : (partialResiduals p t).all (fun e => covered C cs e.snd) = true)
    (m : Machine) (hm : compatible p m) : WeightedBound C m := by
  rcases partialSound B p t hf hno ha m hm with hb|⟨e,he,hm'⟩
  · exact bound_mono hBC hb
  · exact covered_sound (List.all_eq_true.mp hc e he) m hm'

#print axioms cover_of_residuals
end BB6.Agent29ResidualCover
