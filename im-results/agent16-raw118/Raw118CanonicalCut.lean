import Canonical68E1ParentGraft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw118CanonicalCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent6Canonical68E1ParentGraft

/-- Literal E1=0LE cylinder; definition agrees with Raw118Base.parent. -/
abbrev p118 : PartialMachine := refine e1Base (4,true) (some ⟨false,false,4⟩)

theorem parent_root : p118 initialSlot = some (some ⟨true,true,1⟩) := by decide

/-- Reusable cut against any sound quotient roster; the parent proof is
    kept separate to avoid a dependency on its large generated certificate. -/
theorem sound_cut {B : Nat} {roster : List Entry}
    (hB : 756496 ≤ B)
    (hbase : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (h118 : Cover (WeightedBound 756496) p118) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ graftRoster p118 [] roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p118) (replacement := []) (roster := roster)
    parent_root hbase
  intro m hm
  exact Or.inl (fun k d hk hd => Nat.le_trans (h118.sound m hm k d hk hd) hB)

/-- Exact membership in the currently source-audited conditional roster. -/
theorem parent_count68 :
    (roster68.filter (fun e => sameTable e.2 p118)).length = 1 := by decide

noncomputable def roster67 := graftRoster p118 [] roster68

theorem count67 : roster67.length = 67 := by decide

theorem sound67
    (h68 : ∀ m, compatible root m → WeightedBound 6766859 m ∨
      ∃ e ∈ roster68, TNFQuotientCompatible e.2 m)
    (h118 : Cover (WeightedBound 756496) p118) :
    ∀ m, compatible root m → WeightedBound 6766859 m ∨
      ∃ e ∈ roster67, TNFQuotientCompatible e.2 m :=
  sound_cut (by decide) h68 h118

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (h68 : ∀ m, compatible root m → WeightedBound 6766859 m ∨
      ∃ e ∈ roster68, TNFQuotientCompatible e.2 m)
    (h118 : Cover (WeightedBound 756496) p118)
    (hLeaves : ∀ e ∈ roster67, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (sound67 h68 h118) hLeaves champ

#print axioms parent_root
#print axioms sound_cut
#print axioms parent_count68
#print axioms count67
#print axioms sound67
#print axioms exact_at_target

end BB6.Agent16Raw118CanonicalCut
