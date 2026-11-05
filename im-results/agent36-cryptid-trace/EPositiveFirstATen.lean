import EPositiveFirstWalk
namespace BB6.Agent36PositiveFirst
open CryptidBoundary
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem aTenNoPhysical (r : Nat) (L ys : List Bool) :
    NoPhysical (⟨L,false,pairs r ++ ys,0⟩ : Cfg) (2*r) := by
  induction r generalizing L with
  | zero => intro t ht; omega
  | succ r ih =>
    have ht : 2*(r+1)=2+2*r := by omega
    rw [ht]
    exact join
      (⟨L,false,pairs (r+1) ++ ys,0⟩ : Cfg)
      (⟨[false,true] ++ L,false,pairs r ++ ys,0⟩ : Cfg)
      2 (2*r)
      (by
        intro t hb hp
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [PhysicalF0,pairs,run,step,goL,goR] at hp)
      (by
        change run 2
          (⟨L,false,[true,false] ++ (pairs r ++ ys),0⟩ : Cfg) = _
        exact aTenOppStep L (pairs r ++ ys))
      (ih ([false,true] ++ L))

#print axioms aTenNoPhysical
end BB6.Agent36PositiveFirst
