import Raw139SmallPlus
import Raw139E0ZeroLB

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent41Raw139SmallPair
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent41Raw139Small BB6.Agent41Raw139SmallPlus

abbrev pairTable := BB6Coverage.Agent41Raw139ZeroLB.table

def removePair (es : List (List Move × PartialMachine)) :=
  removeTable (pairTable true) (removeTable (pairTable false) es)

theorem removePair_sound (B : Nat) (es : List (List Move × PartialMachine)) (m : Machine)
    (H : WeightedBound B m ∨ ∃ e ∈ es, compatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removePair es, compatible e.2 m :=
  removeTable_sound B (pairTable true) (BB6Coverage.Agent41Raw139ZeroLB.never true)
    (removeTable (pairTable false) es) m
    (removeTable_sound B (pairTable false) (BB6Coverage.Agent41Raw139ZeroLB.never false)
      es m H)

def e0ResidualsPair := removePair e0ResidualsPlus
def residualsPair := removePair residualsPlus

theorem e0_count_pair : e0ResidualsPair.length = 3 := by decide
theorem e0_mass_pair : rawMass e0ResidualsPair = 75 := by decide
theorem parent_count_pair : residualsPair.length = 78 := by decide
theorem parent_mass_pair : rawMass residualsPair = 4793671950 := by decide

theorem e0_contract_pair :
    ∀ m, compatible e0Parent m →
      WeightedBound 512 m ∨ ∃ e ∈ e0ResidualsPair, compatible e.2 m := by
  intro m hm
  exact removePair_sound 512 e0ResidualsPlus m (e0_contract_plus m hm)

theorem parent_contract_pair :
    ∀ m, compatible BB6.Agent41Raw139Small.parent m →
      WeightedBound 512 m ∨ ∃ e ∈ residualsPair, compatible e.2 m := by
  intro m hm
  exact removePair_sound 512 residualsPlus m (parent_contract_plus m hm)

#print axioms removePair_sound
#print axioms e0_count_pair
#print axioms e0_mass_pair
#print axioms parent_count_pair
#print axioms parent_mass_pair
#print axioms e0_contract_pair
#print axioms parent_contract_pair
end BB6.Agent41Raw139SmallPair
