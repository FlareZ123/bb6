import Raw139SmallAudit
import Raw139E0OneLA

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent41Raw139SmallPlus
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent41Raw139Small

abbrev closedTable := BB6Coverage.Agent41Raw139E0OneLA.table

/-- Reusable exact-table removal of a semantically nonhalting residual. -/
def removeTable (p : PartialMachine) (es : List (List Move × PartialMachine)) :
    List (List Move × PartialMachine) :=
  es.filter fun e => !(tableOK e.2 p)

theorem removeTable_sound (B : Nat) (p : PartialMachine)
    (safe : ∀ m, compatible p m → NeverHalts m)
    (es : List (List Move × PartialMachine)) (m : Machine)
    (H : WeightedBound B m ∨ ∃ e ∈ es, compatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeTable p es, compatible e.2 m := by
  rcases H with hw | ⟨e,he,hm⟩
  · exact Or.inl hw
  · by_cases hmatch : tableOK e.2 p = true
    · have heq := tableOK_sound e.2 p hmatch
      rw [heq] at hm
      exact Or.inl (weighted_never B m (safe m hm))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hm⟩

def e0ResidualsPlus := removeTable closedTable e0Residuals
def residualsPlus := removeTable closedTable residuals

theorem e0_count_plus : e0ResidualsPlus.length = 5 := by decide
theorem e0_mass_plus : rawMass e0ResidualsPlus = 125 := by decide
theorem parent_count_plus : residualsPlus.length = 80 := by decide
theorem parent_mass_plus : rawMass residualsPlus = 4793672000 := by decide

theorem e0_contract_plus :
    ∀ m, compatible e0Parent m →
      WeightedBound 512 m ∨ ∃ e ∈ e0ResidualsPlus, compatible e.2 m := by
  intro m hm
  exact removeTable_sound 512 closedTable BB6Coverage.Agent41Raw139E0OneLA.never
    e0Residuals m (e0_contract m hm)

theorem parent_contract_plus :
    ∀ m, compatible parent m →
      WeightedBound 512 m ∨ ∃ e ∈ residualsPlus, compatible e.2 m := by
  intro m hm
  exact removeTable_sound 512 closedTable BB6Coverage.Agent41Raw139E0OneLA.never
    residuals m (BB6.Agent41Raw139Small.parent_contract m hm)

#print axioms removeTable_sound
#print axioms e0_count_plus
#print axioms e0_mass_plus
#print axioms parent_count_plus
#print axioms parent_mass_plus
#print axioms e0_contract_plus
#print axioms parent_contract_plus
end BB6.Agent41Raw139SmallPlus
