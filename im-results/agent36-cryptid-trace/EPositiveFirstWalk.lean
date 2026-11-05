import EPositiveFirstScans
namespace BB6.Agent36PositiveFirst
open CryptidBoundary
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
theorem walkNoPhysical (n : Nat) (L ys : List Bool) :
    NoPhysical (cWalk n L ys) (2*n) := by
  induction n generalizing ys with
  | zero => intro t ht; omega
  | succ n ih =>
    have ht : 2*(n+1)=2+2*n := by omega
    rw [ht]
    exact join (cWalk (n+1) L ys) (cWalk n L (true::true::ys)) 2 (2*n)
      (by
        intro t hb hp
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [PhysicalF0,cWalk,run,step,goL,goR,oppairs] at hp)
      (cWalk_step n L ys) (ih (true::true::ys))
#print axioms walkNoPhysical
end BB6.Agent36PositiveFirst
