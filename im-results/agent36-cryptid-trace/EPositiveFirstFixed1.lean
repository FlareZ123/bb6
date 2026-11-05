import EPositiveFirstDPair
namespace BB6.Agent36PositiveFirst
open CryptidBoundary
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem aSevenNoPhysical (L ys : List Bool) :
    NoPhysical (⟨L,false,[true,true,false] ++ ys,0⟩ : Cfg) 7 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,run,step,goL,goR] at hp

theorem aThreeNoPhysical (r : Nat) (L ys : List Bool) :
    NoPhysical
      (⟨oppairs r ++ ([false,true,true] ++ L),false,false::ys,0⟩ : Cfg)
      3 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 := by omega
  rcases hc with rfl | rfl | rfl
  all_goals simp [PhysicalF0,oppairs,run,step,goL,goR] at hp

theorem dTwoNoPhysical (L ys : List Bool) :
    NoPhysical (⟨[true,true] ++ L,false,ys,3⟩ : Cfg) 2 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [PhysicalF0,run,step,goL,goR] at hp
#print axioms aSevenNoPhysical
#print axioms aThreeNoPhysical
#print axioms dTwoNoPhysical
end BB6.Agent36PositiveFirst
