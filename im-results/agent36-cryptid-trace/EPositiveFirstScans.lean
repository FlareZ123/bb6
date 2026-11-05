import EPositiveFirstPrelude
namespace BB6.Agent36PositiveFirst
open CryptidBoundary
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
theorem scanNoPhysical (n : Nat) (L ys : List Bool) :
    NoPhysical (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero => intro t ht; omega
  | succ n ih =>
    have ht : 2*(n+1)=2+2*n := by omega
    rw [ht]
    exact join (scanStart (n+1) L ys)
      (scanStart n ([false,true]++L) ys) 2 (2*n)
      (by
        intro t hb hp
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [PhysicalF0,scanStart,run,step,goL,goR,pairs] at hp)
      (scan_step n L ys) (ih ([false,true]++L) ys)
#print axioms scanNoPhysical
end BB6.Agent36PositiveFirst
