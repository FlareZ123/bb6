import EPositiveFirstComplete

namespace BB6.Agent36EZeroFirst
open CryptidBoundary
open BB6.Agent36EZeroPairs0
open BB6.Agent36PositiveFirst

set_option maxHeartbeats 100000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- No physical return in the first four original E-side transitions. -/
theorem eFourNoPhysical (m r : Nat) (ys : List Bool) :
    NoPhysical (ePairZero m r ys) 4 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,ePairZero,run,step,goL,goR,pairs,
    List.append_assoc] at hp

/-- This 44-step original D transition crosses F twice with marked cells
    still to the left, and reaches the B sweep with no physical F/0 return. -/
theorem dTailNoPhysical (m : Nat) (ys : List Bool) :
    NoPhysical (⟨leftCarrier m,true,
      [true,true,true,true] ++ ys,3⟩ : Cfg) 44 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 ∨ t=17 ∨ t=18 ∨ t=19 ∨ t=20 ∨ t=21 ∨ t=22 ∨ t=23 ∨ t=24 ∨ t=25 ∨ t=26 ∨ t=27 ∨ t=28 ∨ t=29 ∨ t=30 ∨ t=31 ∨ t=32 ∨ t=33 ∨ t=34 ∨ t=35 ∨ t=36 ∨ t=37 ∨ t=38 ∨ t=39 ∨ t=40 ∨ t=41 ∨ t=42 ∨ t=43 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,leftCarrier,run,step,goL,goR,
    pairs,oppairs,List.append_assoc] at hp

#print axioms eFourNoPhysical
#print axioms dTailNoPhysical
end BB6.Agent36EZeroFirst
