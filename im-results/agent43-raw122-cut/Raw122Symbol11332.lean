import Raw122Compact11332
import NGramCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1NGram.Raw122Symbol11332
open BB6Coverage BB6.Agent1NGram

def p11332 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true, true, 1⟩)
  | (0, true) => some (some ⟨false, false, 0⟩)
  | (1, false) => some (some ⟨true, true, 2⟩)
  | (1, true) => some (some ⟨false, false, 1⟩)
  | (2, false) => some (some ⟨false, true, 3⟩)
  | (2, true) => some (some ⟨false, false, 4⟩)
  | (3, false) => some (some ⟨true, false, 3⟩)
  | (3, true) => some (some ⟨true, true, 4⟩)
  | (4, false) => some (some ⟨false, true, 0⟩)
  | (4, true) => some (some ⟨false, false, 5⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨true, false, 1⟩)
  | _ => none
theorem never11332 (m : Machine) (hm : compatible p11332 m) : NeverHalts m := by
  apply BB6Coverage.Agent31Pump.Raw122DirectGrowth.M11332Compact.never m
  have he : BB6Coverage.Agent31Pump.Raw122DirectGrowth.M11332Compact.table = p11332 := by
    funext s
    rcases s with ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
  rw [he]
  exact hm
#print axioms never11332
end BB6.Agent1NGram.Raw122Symbol11332
