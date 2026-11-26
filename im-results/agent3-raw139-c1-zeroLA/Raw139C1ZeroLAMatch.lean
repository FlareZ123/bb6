import Raw139Normalized
import ThreeHoleAudit
namespace BB6.Agent3Raw139C1ZeroLAMatch
open BB6Coverage BB6Coverage.FAR BB6.Agent6Raw139Normalized BB6.Agent31ThreeHole

def row : Fin 7 × Move := (4,⟨false,false,0⟩)
theorem member : row ∈ remainingRows := by decide
theorem exact_table : leaf row = fromCodes [7,24,11,24,14,0,3,16,12,11,24,24] := tableOK_sound _ _ (by decide)
#print axioms member
#print axioms exact_table
end BB6.Agent3Raw139C1ZeroLAMatch
