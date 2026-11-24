import SevenRoster
import SideWitnessCore

set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace BB6.Agent47SevenSideWitnesses
open BB6.Agent47SevenRoster

def reducedSevenRoster : List PackedResidual :=
  sevenRoster.filter fun e => !hasWitness e.2

theorem reducedSevenRoster_sound : Covered 7014 reducedSevenRoster := by
  intro m hm
  rcases sevenRoster_sound m hm with hb | ⟨e,hmem,hcomp⟩
  · exact Or.inl hb
  · cases he : hasWitness e.2 with
    | true => exact Or.inl (hasWitness_sound e.2 he m hcomp)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨hmem,by simp [he]⟩,hcomp⟩

#eval reducedSevenRoster.length
#print axioms reducedSevenRoster_sound
end BB6.Agent47SevenSideWitnesses
