import Agent46Raw13Upstream
import Raw13BinarySiblings

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13BinaryGraft
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole
open BB6.Agent46CanonicalCut BB6.Agent46Raw13 BB6.Agent47WeightedHalt
open BB6.Agent46Raw13Upstream BB6.Agent46Raw13BinarySiblings

def variants : List Variant := [.zeroLA,.oneRA,.zeroLE,.oneLE,.oneRC]
def closedFive (e : Entry) : Bool := variants.any (fun v => tableOK e.2 (p v))
def independentRs2 := (residuals parent2 5 cut2).filter (fun e => !closedFive e)
def improvedRs2 := rs2.filter (fun e => !closedFive e)

theorem filterFive_sound (xs : List Entry) (m : Machine)
    (h : WeightedBound 21269 m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ xs.filter (fun e => !closedFive e), TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  by_cases hc : closedFive e = true
  · obtain ⟨v,hv,ht⟩ := List.any_eq_true.mp hc
    have hq' : TNFQuotientCompatible (p v) m := tableOK_sound _ _ ht ▸ hq
    have hroot : p v initialSlot = some (some ⟨true,true,1⟩) := by cases v <;> decide
    exact Or.inl (safe_quotient hroot (fun m' hm' => weighted_never 21269 m' (never v m' hm')) m hq')
  · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hc]⟩,hq⟩

theorem independent_sound2 (m : Machine) (hm : TNFQuotientCompatible parent2 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ independentRs2, TNFQuotientCompatible e.2 m :=
  filterFive_sound _ m (sound 21269 parent2 5 cut2 (by decide) p2_3_support (by decide) p2_3_nohalt checked2 m hm)

theorem improved_sound2 (h : NeverHalts candidate2) (m : Machine) (hm : TNFQuotientCompatible parent2 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ improvedRs2, TNFQuotientCompatible e.2 m :=
  filterFive_sound _ m (sound2 h m hm)

def improved := (raw13Residuals.flatMap (replace parent1 rs1)).flatMap (replace parent2 improvedRs2)

theorem improved_sound (h1 : NeverHalts candidate1) (h2 : NeverHalts candidate2)
    (m : Machine) (hm : TNFQuotientCompatible raw13 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ improved, TNFQuotientCompatible e.2 m :=
  replace_sound _ _ _ m (replace_sound _ _ _ m (raw13_sound m hm) (sound1 h1 m)) (improved_sound2 h2 m)

theorem independent_count : independentRs2.length = 77 := by decide
theorem improved_count2 : improvedRs2.length = 76 := by decide
theorem improved_count : improved.length = 1838 := by decide
#print axioms independent_sound2
#print axioms improved_sound
#print axioms improved_count
end BB6.Agent46Raw13BinaryGraft
