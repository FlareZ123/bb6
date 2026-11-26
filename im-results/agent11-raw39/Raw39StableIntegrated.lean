import Raw39StableCut
import Raw39Data
import Raw39B0RBData
import Raw39B1RCData
import Raw39B0REData

namespace BB6.Agent11Raw39Stable
open BB6Coverage BB6.Agent13BlankDelay

/-- The accepted child theorems instantiate the stable parent cut directly. -/
theorem cut_integrated : ∀ m, compatible p39 m →
    WeightedBound 1882 m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  cut_sound BB6.Agent11Raw39B0RB.allChild BB6.Agent11Raw39.all1RB
    BB6.Agent11Raw39B1RC.allChild BB6.Agent11Raw39B0RE.allChild

#print axioms cut_integrated
end BB6.Agent11Raw39Stable
