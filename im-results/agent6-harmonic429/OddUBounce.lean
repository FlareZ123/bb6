import OddBoundary
import Lean.Elab.Tactic.Omega

/-!
An additional parameter-uniform #429 affine corridor, at U_k with
k = 3 (mod 4), w = 3 (mod 4). The two-step overflow, two-step
odd-odd reset and k first-branch iterations give an exact k+4 return.

This is a conditional transition theorem with no claim of all-time
blank-root nonhalting. The lower overflow condition, upper reset margin
and finite guards are all explicit.
-/
namespace BB429OddUBounce
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

/-- A new U-odd bounce for k congruent to 3 modulo 4. -/
theorem odd_U_bounce (k w:Nat) (hk:3≤k) (hkm:k%4=3) (hwm:w%4=3)
  (hcap:w+7≤2*rayU k) (hover:2*rayU k+22≤3*w)
  (hreset:11*w≤10*rayU k+103):
    run (k+4) (rayU k,w)=some (rayU k,w+3*k+31) := by
  let u:=rayU k
  let x:=2*u-w+18
  let y:=3*w-2*u-22
  have hu4:u%4=1:=by dsimp [u];exact U_mod k (by omega)
  have hxodd:x%2=1:=by dsimp [x];omega
  have hxlarge:3≤x:=by dsimp [x];omega
  have hymod:y%4=1:=by dsimp [y];omega
  have hxyguard:3*y≤2*x+1:=by dsimp [x,y];omega
  have hcases:=BB429OddBoundary.rayU_odd_boundary k w hk hwm hcap
  have hFirst:run 2 (u,w)=some (x,y):=by
    rcases hcases with ⟨hr,_⟩ | ⟨_,hs⟩
    · exact False.elim (by omega : False)
    · simpa only [u,x,y] using hs
  have hSecond:=BB429OddExtension.odd_odd_two_step x y hxodd hxlarge hymod hxyguard
  have hW:2*x+y+17=2*u+w+31:=by dsimp [x,y];omega
  have hBal:=ray_balance k
  have hdb:rayDemand k≤2*u+w+31:=by dsimp [u] at *;omega
  have hray:=ray_run k (2*u+w+31) hdb
  have hfinal:(2*u+w+31)-rayDemand k=w+3*k+31:=by dsimp [u] at *;omega
  have hfour:run 4 (u,w)=some (0,2*u+w+31):=by
    rw [show 4=2+2 by decide,BB429.run_add,hFirst]
    simpa only [Option.bind_some,hW] using hSecond
  rw [show k+4=4+k by omega,BB429.run_add,hfour]
  simpa only [Option.bind_some,u,hfinal] using hray

/-- A bounded affine U-odd family, with arbitrary finite repeat count. -/
theorem odd_U_ladder (k n w:Nat) (hk:3≤k) (hkm:k%4=3)
  (hwm:w%4=3) (hover:2*rayU k+22≤3*w)
  (hbound:w+n*(3*k+31)+7≤2*rayU k)
  (hreturn:11*(w+n*(3*k+31))≤10*rayU k+103):
  run (n*(k+4)) (rayU k,w)=some (rayU k,w+n*(3*k+31)) := by
  have hdmod:(3*k+31)%4=0:=by omega
  induction n with
  | zero => simp [BB429.run]
  | succ n ih =>
    have hboundN:w+n*(3*k+31)+7≤2*rayU k:=by
      rw [Nat.succ_mul n (3*k+31)] at hbound
      omega
    have hreturnN:11*(w+n*(3*k+31))≤10*rayU k+103:=by
      rw [Nat.succ_mul n (3*k+31)] at hreturn
      omega
    have hwmN:(w+n*(3*k+31))%4=3:=by
      simp [Nat.add_mod,Nat.mul_mod,hwm,hdmod]
    have hoverN:2*rayU k+22≤3*(w+n*(3*k+31)):=by omega
    have hStep:=odd_U_bounce k (w+n*(3*k+31)) hk hkm hwmN
      hboundN hoverN hreturnN
    rw [Nat.succ_mul, BB429.run_add,ih hboundN hreturnN]
    simp only [Option.bind_some,hStep]
    have hEq:w+n*(3*k+31)+3*k+31=w+(n+1)*(3*k+31):=by
      rw [Nat.succ_mul n (3*k+31)]
      omega
    exact congrArg (fun z:Nat=>some (rayU k,z)) hEq

/-- The first genuine U-seven bounce is the next segment after macro 222. -/
theorem actual_U7_bounce : run 11 (rayU 7,319)=some (rayU 7,371) := by
  have h:=odd_U_bounce 7 319 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  simpa using h

#print axioms odd_U_bounce
#print axioms odd_U_ladder
#print axioms actual_U7_bounce
end BB429OddUBounce
