import Box27CanonicalAfter12V02
import Box27Orbit14V18Source
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49.Box27CanonicalAfter14V18
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49.Box27CanonicalFrontier
open BB6.Agent49Box BB6.Agent49BoxBridge

def remaining (d v : Fin 25) : Bool := Box27CanonicalAfter12V02.remaining d v && !decide (d=14 ∧ v=18)

def keys : List (Fin 25 × Fin 25) := canonicalKeys.filter (fun (d,v) => remaining d v)

theorem remainingCount : keys.length = 126 := by decide

theorem cover_iff_remaining (B : Nat) (hB : 255 ≤ B) :
    (∀ m, Fits raw10Remainder[27]! m → WeightedBound B m) ↔
    (∀ d v : Fin 25, remaining d v = true → ∀ m, child d v m → WeightedBound B m) := by
  constructor
  · intro h d v hc m hm; exact h m hm.1
  · intro h
    apply (Box27CanonicalAfter12V02.cover_iff_remaining B hB).2
    intro d v hc m hm
    by_cases he : d=14 ∧ v=18
    · rcases he with ⟨rfl,rfl⟩
      intro k e hk hd
      exact Nat.le_trans (BB6.Agent49.Box27Orbit14V18.source_bound m hm k e hk hd) hB
    · exact h d v (by simp [remaining,hc,he]) m hm

#print axioms remainingCount
#print axioms cover_iff_remaining
end BB6.Agent49.Box27CanonicalAfter14V18
