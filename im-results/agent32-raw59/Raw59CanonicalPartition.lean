import Raw59ParentPartition
import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Raw59Partition
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent32Raw59

def address : List Move :=
  [⟨true,true,2⟩, ⟨false,true,3⟩, ⟨true,false,3⟩,
   ⟨true,true,4⟩, ⟨true,false,0⟩]

theorem raw59_mem : (address,p59) ∈ BB6.Agent47Canonical78.roster := by
  have h : BB6.Agent47Canonical78.roster.any
      (fun e => decide (e.1 = address) && tableOK e.2 p59) = true := by decide
  obtain ⟨e,he,hc⟩ := List.any_eq_true.mp h
  have ha : e.1 = address := of_decide_eq_true (Bool.and_eq_true.mp hc).1
  have hp : e.2 = p59 := tableOK_sound _ _ (Bool.and_eq_true.mp hc).2
  have hEq : e = (address,p59) := Prod.ext ha hp
  simpa only [hEq] using he

theorem cover_at_target (B : Nat) (hB : 7014 ≤ B) (closed : Move → Bool)
    (hs : ∀ mv, closed mv = true → ∀ m, compatible (child mv) m → WeightedBound 395 m)
    (ho : ∀ e ∈ BB6.Agent47Canonical78.roster, e.2 ≠ p59 → Cover (WeightedBound B) e.2)
    (hr : ∀ mv ∈ retained closed, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder := by
  apply BB6.Agent47Canonical78.cover_at_target B hB
  intro e he
  by_cases eq : e.2 = p59
  · rw [eq]
    exact cover_raw59 B (by omega) closed hs hr
  · exact ho e he eq

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B) (closed : Move → Bool)
    (hs : ∀ mv, closed mv = true → ∀ m, compatible (child mv) m → WeightedBound 395 m)
    (ho : ∀ e ∈ BB6.Agent47Canonical78.roster, e.2 ≠ p59 → Cover (WeightedBound B) e.2)
    (hr : ∀ mv ∈ retained closed, Cover (WeightedBound B) (child mv))
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47Canonical78.exact_at_target B hB _ champ
  intro e he
  by_cases eq : e.2 = p59
  · rw [eq]
    exact cover_raw59 B (by omega) closed hs hr
  · exact ho e he eq

#print axioms raw59_mem
#print axioms cover_at_target
#print axioms exact_at_target
end BB6.Agent32Raw59Partition
