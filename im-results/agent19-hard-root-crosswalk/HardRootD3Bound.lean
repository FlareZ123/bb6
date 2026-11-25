import Lean.Elab.Tactic.Omega
import WeightedFirstOneCover
import FirstHolePath

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-
A lightweight, source-local copy of the HardRootLeaves D3 leaf certificate.
Keeping this module independent of HardRootLeaves avoids importing the entire
raw114 accepted-source closure merely to reuse this 25² cylinder.
-/
namespace BB6.Agent46Raw13D3
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

def D3 : Machine := literal [
  some ⟨true,true,1⟩,
  some ⟨false,false,2⟩,
  some ⟨true,true,2⟩,
  some ⟨true,true,4⟩,
  some ⟨true,false,0⟩,
  some ⟨false,false,3⟩,
  some ⟨false,true,1⟩,
  some ⟨false,true,0⟩,
  some ⟨true,true,1⟩,
  some ⟨true,true,5⟩,
  some ⟨true,true,3⟩,
  none
]

def d3Leaf : PartialMachine := forgetHaltRows D3

def D3_schedule : List (Nat × Slot) :=
  [(1,(1,false)), (2,(2,false)), (3,(0,true)), (4,(2,true)),
   (5,(3,false)), (11,(1,true)), (12,(4,false)), (14,(4,true)),
   (15,(5,false)), (23,(3,true))]

theorem D3_path : FirstHolePath d3Leaf 6 :=
  checked_from_root _ D3_schedule (by decide)

theorem D3_cover_iff (B : Nat) :
    Cover (WeightedBound B) d3Leaf ↔
      ∀ k, HaltsAfter D3 k → k+1+0 ≤ B := by
  have hh : D3 (5,true) = none := by decide
  have ho : ∀ t, t ≠ (5,true) → ∃ mv, D3 t = some mv := by
    intro t ht
    have h : D3 t ≠ none := by decide
    cases hD : D3 t with
    | none => exact False.elim (h hD)
    | some mv => exact ⟨mv,hD⟩
  have hD : 0 ∈ delays (zeroNext D3) 0 := by decide
  have hmax : ∀ d ∈ delays (zeroNext D3) 0, d ≤ 0 := by decide
  exact oneHalt_cover_iff_max B D3 (5,true) 0 hh ho hD hmax

theorem D3_haltsAfter23 : HaltsAfter D3 23 := by
  decide

theorem D3_halt_bound24 :
    ∀ k, HaltsAfter D3 k → k + 1 ≤ 24 := by
  intro k hk
  have heq := halting_time_unique D3 k 23 hk D3_haltsAfter23
  omega

/-- All completions of the two-hole D3 halt-row cylinder have primitive
    score at most 24. -/
theorem D3_cover24 : Cover (WeightedBound 24) d3Leaf :=
  (D3_cover_iff 24).2 D3_halt_bound24

#print axioms D3_path
#print axioms D3_cover_iff
#print axioms D3_haltsAfter23
#print axioms D3_halt_bound24
#print axioms D3_cover24

end BB6.Agent46Raw13D3
