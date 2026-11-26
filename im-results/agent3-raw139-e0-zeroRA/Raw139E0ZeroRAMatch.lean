import Raw139Normalized
import ThreeHoleAudit
namespace BB6.Agent3Raw139E0ZeroRAMatch
open BB6Coverage BB6Coverage.FAR BB6.Agent6Raw139Normalized BB6.Agent31ThreeHole
def row : Fin 7 × Move := (2,⟨false,true,0⟩)
theorem member : row ∈ remainingRows := by decide
theorem exact_table : leaf row = fromCodes [7,24,11,24,14,24,24,16,1,11,24,24] := tableOK_sound _ _ (by decide)
theorem exact_member : fromCodes [7,24,11,24,14,24,24,16,1,11,24,24] ∈ remainingTables := by
  rw [← exact_table]
  exact List.mem_map.mpr ⟨row,member,rfl⟩
#print axioms member
#print axioms exact_table
#print axioms exact_member
end BB6.Agent3Raw139E0ZeroRAMatch
