import FastThreeHoleAudit

namespace BB6.Agent14Raw139Cycles
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent50SideCycle BB6.Agent13BlankDelay

def e0 (v : Nat) : PartialMachine := fromCodes [7,24,11,24,14,24,24,16,v,11,24,24]
def d0 (v : Nat) : PartialMachine := fromCodes [7,24,11,24,14,24,v,16,12,11,24,24]

theorem e0_16_check : fastSideCycleCheck (e0 16) 7 1 false (-1) = true := by decide

theorem e0_16_never : ∀ m, compatible (e0 16) m → NeverHalts m :=
  fastSideCycleCheck_sound (e0 16) 7 1 false (-1) (by decide) e0_16_check

theorem e0_18_check : fastSideCycleCheck (e0 18) 7 1 false (-1) = true := by decide

theorem e0_18_never : ∀ m, compatible (e0 18) m → NeverHalts m :=
  fastSideCycleCheck_sound (e0 18) 7 1 false (-1) (by decide) e0_18_check

theorem d0_8_check : fastSideCycleCheck (d0 8) 8 2 false (-2) = true := by decide

theorem d0_8_never : ∀ m, compatible (d0 8) m → NeverHalts m :=
  fastSideCycleCheck_sound (d0 8) 8 2 false (-2) (by decide) d0_8_check

theorem d0_10_check : fastSideCycleCheck (d0 10) 8 2 false (-2) = true := by decide

theorem d0_10_never : ∀ m, compatible (d0 10) m → NeverHalts m :=
  fastSideCycleCheck_sound (d0 10) 8 2 false (-2) (by decide) d0_10_check

theorem d0_12_check : fastSideCycleCheck (d0 12) 8 1 false (-2) = true := by decide

theorem d0_12_never : ∀ m, compatible (d0 12) m → NeverHalts m :=
  fastSideCycleCheck_sound (d0 12) 8 1 false (-2) (by decide) d0_12_check

theorem d0_13_check : fastSideCycleCheck (d0 13) 18 1 true (0) = true := by decide

theorem d0_13_never : ∀ m, compatible (d0 13) m → NeverHalts m :=
  fastSideCycleCheck_sound (d0 13) 18 1 true (0) (by decide) d0_13_check

theorem d0_14_check : fastSideCycleCheck (d0 14) 8 1 false (-2) = true := by decide

theorem d0_14_never : ∀ m, compatible (d0 14) m → NeverHalts m :=
  fastSideCycleCheck_sound (d0 14) 8 1 false (-2) (by decide) d0_14_check

theorem d0_16_check : fastSideCycleCheck (d0 16) 7 2 false (-1) = true := by decide

theorem d0_16_never : ∀ m, compatible (d0 16) m → NeverHalts m :=
  fastSideCycleCheck_sound (d0 16) 7 2 false (-1) (by decide) d0_16_check

theorem d0_18_check : fastSideCycleCheck (d0 18) 7 2 false (-1) = true := by decide

theorem d0_18_never : ∀ m, compatible (d0 18) m → NeverHalts m :=
  fastSideCycleCheck_sound (d0 18) 7 2 false (-1) (by decide) d0_18_check

/-- Exact side-cycle certificates; no assumption on the undefined slots. -/
def closed : List PartialMachine :=
  [e0 16, e0 18, d0 8, d0 10, d0 12, d0 13, d0 14, d0 16, d0 18]

theorem closed_never (p : PartialMachine) (hp : p ∈ closed) :
    ∀ m, compatible p m → NeverHalts m := by
  simp only [closed, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e0_16_never
  · exact e0_18_never
  · exact d0_8_never
  · exact d0_10_never
  · exact d0_12_never
  · exact d0_13_never
  · exact d0_14_never
  · exact d0_16_never
  · exact d0_18_never

/-- Stable weighted contract for every target bound, including zero. -/
theorem closed_cover (B : Nat) (p : PartialMachine) (hp : p ∈ closed) :
    Cover (WeightedBound B) p :=
  Cover.leaf p (fun m hm => weighted_never B m (closed_never p hp m hm))

#print axioms closed_never
#print axioms closed_cover
end BB6.Agent14Raw139Cycles
