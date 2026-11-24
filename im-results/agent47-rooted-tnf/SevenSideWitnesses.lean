import SevenRoster
import SideWitnessCore

set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace BB6.Agent47SevenSideWitnesses
open BB6.Agent47SevenRoster

def reducedSevenRoster : List BB6.Agent50RootFrontier.PackedResidual :=
  sevenRoster.filter fun (e : BB6.Agent50RootFrontier.PackedResidual) =>
    !hasWitness (Prod.snd e)

theorem reducedSevenRoster_sound : Covered 7014 reducedSevenRoster := by
  intro m hm
  rcases sevenRoster_sound m hm with hb | ⟨e,hmem,hcomp⟩
  · exact Or.inl hb
  · cases he : hasWitness (Prod.snd e) with
    | true => exact Or.inl (hasWitness_sound (Prod.snd e) he m hcomp)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨hmem,by simp [he]⟩,hcomp⟩

#eval reducedSevenRoster.length
#print axioms reducedSevenRoster_sound
end BB6.Agent47SevenSideWitnesses
