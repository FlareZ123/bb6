import Agent46Raw13Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13LEPrune
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent46Raw13 BB6.Agent31ThreeHole

def corridor : PartialMachine := refine (refine (child ⟨true,false,2⟩) (2,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,3⟩)
def zeroLE := refine corridor (3,false) (some ⟨false,false,4⟩)
def oneLE := refine corridor (3,false) (some ⟨true,false,4⟩)
abbrev Entry := List Move × PartialMachine

def removeLE (e : Entry) : Bool := tableOK e.2 zeroLE || tableOK e.2 oneLE
def remainder : List Entry := raw13Residuals.filter fun e => !removeLE e

theorem zero_root : zeroLE initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem one_root : oneLE initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem prune_count : remainder.length = 1706 := by decide

theorem prune_sound
    (hz : ∀ m, compatible zeroLE m → WeightedBound 7014 m)
    (ho : ∀ m, compatible oneLE m → WeightedBound 7014 m)
    (m : Machine) (hm : TNFQuotientCompatible raw13 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ remainder, TNFQuotientCompatible e.2 m := by
  rcases raw13_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · cases hzero : tableOK e.2 zeroLE
    case true =>
      have heq := tableOK_sound e.2 zeroLE hzero
      have hb := safe_quotient zero_root hz m (heq ▸ hq)
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    case false =>
      cases hone : tableOK e.2 oneLE
      case true =>
        have heq := tableOK_sound e.2 oneLE hone
        have hb := safe_quotient one_root ho m (heq ▸ hq)
        exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
      case false =>
        exact Or.inr ⟨e, List.mem_filter.mpr ⟨he,by simp [removeLE,hzero,hone]⟩,hq⟩

#print axioms prune_count
#print axioms prune_sound
end BB6.Agent46Raw13LEPrune
