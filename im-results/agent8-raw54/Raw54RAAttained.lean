import Raw54RABase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA
open BB6Coverage BB6.Agent13BlankDelay

def witness1 := refine parent (0,true) (some ⟨true,false,5⟩)
def witness2 := refine witness1 (1,true) (some ⟨false,true,2⟩)
def witness3 := refine witness2 (2,true) (some ⟨true,true,0⟩)
def witness4 := refine witness3 (5,true) (some ⟨false,false,0⟩)
def witness : Machine := weightedTNFDefaultCompletion (refine witness4 (5,false) none)

theorem witness_compatible : compatible parent witness := by
  have h4 := weightedTNFDefaultCompletion_compatible (refine witness4 (5,false) none)
  have h3 : compatible witness4 witness := refine_preserves_compat witness4 witness (5,false) none (by decide) h4
  have h2 : compatible witness3 witness := refine_preserves_compat witness3 witness (5,true) (some ⟨false,false,0⟩) (by decide) h3
  have h1 : compatible witness2 witness := refine_preserves_compat witness2 witness (2,true) (some ⟨true,true,0⟩) (by decide) h2
  have h0 : compatible witness1 witness := refine_preserves_compat witness1 witness (1,true) (some ⟨false,true,2⟩) (by decide) h1
  exact refine_preserves_compat parent witness (0,true) (some ⟨true,false,5⟩) (by decide) h0

theorem witness_halts : HaltsAfter witness 361 := by
  have hr : (knownRun witness4 361).map readSlot = some (5,false) := by decide
  have hh : witness4 (5,false) = none := by decide
  have hm : compatible (refine witness4 (5,false) none) witness := weightedTNFDefaultCompletion_compatible _
  cases hrun : knownRun witness4 361 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (5,false) := by simpa [hrun] using hr
    apply first_hole_halts witness4 361 c hrun
    · simpa [hs] using hh
    · simpa [hs] using hm

theorem witness_delay : 1 ∈ delays (zeroNext witness) 0 := by decide

theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m 361 ∧ 1 ∈ delays (zeroNext m) 0 :=
  ⟨witness, witness_compatible, witness_halts, witness_delay⟩

theorem lower_bound (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : 363 ≤ B := by
  have hb := h witness witness_compatible 361 1 witness_halts witness_delay
  omega
#print axioms attained
#print axioms lower_bound
end BB6.Agent8Raw54.RA
