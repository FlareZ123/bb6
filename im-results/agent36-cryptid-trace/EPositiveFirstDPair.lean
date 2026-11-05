import EPositiveFirstATen
namespace BB6.Agent36PositiveFirst
open CryptidBoundary
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem dTwoStep (r : Nat) (L ys : List Bool) :
    run 2 (⟨pairs (r+1) ++ L,false,ys,3⟩ : Cfg) =
    ⟨pairs r ++ L,false,[true,true] ++ ys,3⟩ := by
  simp [run,step,goL,goR,pairs]

theorem dPairsNoPhysical (r : Nat) (L ys : List Bool) :
    NoPhysical (⟨pairs r ++ L,false,ys,3⟩ : Cfg) (2*r) := by
  induction r generalizing ys with
  | zero => intro t ht; omega
  | succ r ih =>
    have ht : 2*(r+1)=2+2*r := by omega
    rw [ht]
    exact join
      (⟨pairs (r+1) ++ L,false,ys,3⟩ : Cfg)
      (⟨pairs r ++ L,false,[true,true] ++ ys,3⟩ : Cfg)
      2 (2*r)
      (by
        intro t hb hp
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [PhysicalF0,pairs,run,step,goL,goR] at hp)
      (dTwoStep r L ys)
      (ih ([true,true] ++ ys))
#print axioms dPairsNoPhysical
end BB6.Agent36PositiveFirst
