import EPositiveFirstFixed1

namespace BB6.Agent36PositiveFirst
open CryptidBoundary
open BB6.Agent36PositiveDoubleZero

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- The E-to-A four-step middle bridge may visit state F, but not with a physically blank left tape. -/
theorem dBridgeNoPhysical (m q r : Nat) (ys : List Bool) :
    NoPhysical
      (⟨oppairs (q+2) ++ core m,true,
        [true,true] ++ (List.replicate (2*r) true ++
          ([true,true] ++ ys)),3⟩ : Cfg)
      4 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,run,step,goL,goR,oppairs,core,pairs,
    List.any_append, List.append_assoc] at hp

/-- The four-step C-base turn also has no physically blank-left F/0 visit. -/
theorem cBaseNoPhysical (m q r : Nat) (ys : List Bool) :
    NoPhysical
      (⟨core m,true,
        List.replicate (2*q) true ++
          ([true,false,true,true] ++
            (List.replicate (2*r+4) true ++ ys)),2⟩ : Cfg)
      4 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,run,step,goL,goR,oppairs,core,pairs,
    List.any_append, List.append_assoc] at hp

#print axioms dBridgeNoPhysical
#print axioms cBaseNoPhysical
end BB6.Agent36PositiveFirst
