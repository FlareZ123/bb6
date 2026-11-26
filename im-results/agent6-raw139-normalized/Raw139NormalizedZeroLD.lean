import Raw139Normalized
import ChampionF1ZeroLDCover
namespace BB6.Agent6Raw139Normalized
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster

def rowZeroLD : Fin 7 × Move := (5,⟨false,false,3⟩)
def remaining66 := remainingRows.filter (· != rowZeroLD)
theorem count66 : remaining66.length = 66 := by decide
theorem zeroLD_exact : sameTable (leaf rowZeroLD) BB6.Agent48F1ZeroLD.parent = true := by decide
theorem zeroLD_cover (B : Nat) (h : 124 ≤ B) : Cover (WeightedBound B) (leaf rowZeroLD) := by
  rw [sameTable_sound zeroLD_exact]
  exact Cover.leaf _ (fun m hm k d hk hd => Nat.le_trans (BB6.Agent48F1ZeroLD.all_completions_weighted m hm k d hk hd) h)
theorem consumeZeroLD (B : Nat) (h : 124 ≤ B)
    (hl : ∀ p ∈ remaining66.map leaf, Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p := by
  intro p hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  by_cases he : r = rowZeroLD
  · subst r
    exact zeroLD_cover B h
  · exact hl (leaf r) (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,by simp [he]⟩,rfl⟩)
#print axioms zeroLD_cover
#print axioms consumeZeroLD
end BB6.Agent6Raw139Normalized
