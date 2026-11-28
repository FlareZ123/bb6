import Raw44B1RCComplete
import Raw44Old0LAAssembled
import Raw44Old0LEAssembled
import Raw44Old0RAAssembled
import Raw44Old0REAssembled
import Raw44Old1RAClosed

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw44B1RCJoin
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit

theorem old0LA_adapter (m : Machine) (hm : compatible (child (some ⟨false,false,0⟩)) m) : WeightedBound 126 m := by
  have he : (child (some ⟨false,false,0⟩)) = BB6.Agent16Raw44Old0LA.parent := tableOK_sound _ _ (by decide +kernel)
  rw [he] at hm
  exact BB6.Agent16Raw44Old0LA.weighted_bound m hm

theorem old0LE_adapter (m : Machine) (hm : compatible (child (some ⟨false,false,4⟩)) m) : WeightedBound 373 m := by
  have he : (child (some ⟨false,false,4⟩)) = BB6.Agent16Raw44Old0LE.parent := tableOK_sound _ _ (by decide +kernel)
  rw [he] at hm
  exact BB6.Agent16Raw44Old0LE.weighted_bound m hm

theorem old0RA_adapter (m : Machine) (hm : compatible (child (some ⟨false,true,0⟩)) m) : WeightedBound 375 m := by
  have he : (child (some ⟨false,true,0⟩)) = BB6.Agent16Raw44Old0RA.parent := tableOK_sound _ _ (by decide +kernel)
  rw [he] at hm
  exact BB6.Agent16Raw44Old0RA.weighted_bound m hm

theorem old0RE_adapter (m : Machine) (hm : compatible (child (some ⟨false,true,4⟩)) m) : WeightedBound 211 m := by
  have he : (child (some ⟨false,true,4⟩)) = BB6.Agent16Raw44Old0RE.parent := tableOK_sound _ _ (by decide +kernel)
  rw [he] at hm
  exact BB6.Agent16Raw44Old0RE.weighted_bound m hm

theorem old1RA_adapter (m : Machine) (hm : compatible (child (some ⟨true,true,0⟩)) m) : WeightedBound 211 m := by
  have he : (child (some ⟨true,true,0⟩)) = BB6.Agent16Raw44Old1RA.parent := tableOK_sound _ _ (by decide +kernel)
  rw [he] at hm
  exact BB6.Agent8Raw44Old1RAClosed.weighted_bound m hm

theorem complete_cover : Cover (WeightedBound 475) parent :=
  complete old0LA_adapter old0LE_adapter old0RA_adapter old0RE_adapter old1RA_adapter
#print axioms complete_cover
end BB6.Agent16Raw44B1RCJoin
