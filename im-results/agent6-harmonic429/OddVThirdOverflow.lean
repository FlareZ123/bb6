import OddVHigh
import Lean.Elab.Tactic.Omega

/-!
An exact third-stage, odd V_k overflow: two initial odd-one transitions,
two consecutive first-branch transitions, then a two-step odd-odd reset.
Under a demand guard it continues along the source-transcribed U_(k+3) ray.

All statements are conditional finite accelerated #429 transitions.
-/
namespace BB429OddVThirdOverflow
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

/-- Two consecutive first-branch moves after the odd-one overflow. -/
theorem odd_V_two_first (v w:Nat) (hv:v%4=1) (hw:w%4=1)
    (hcap:w+7≤2*v)
    (hfirst:6*v+33≤5*w)
    (hsecond:14*v+82≤9*w):
    run 4 (v,w)=some ((8*v+49)-4*w,9*w-14*v-82) := by
  let x:=2*v-w+10
  let y:=3*w-2*v-10
  let q:=2*x+3
  let r:=y-2*x-3
  let a:=2*q+3
  let b:=r-2*q-3
  have hvodd:v%2=1:=by omega
  have hInitial:2*v+13≤3*w:=by omega
  have hTwo:=BB429OddCascade.odd_one_overflow_two_step v w hvodd hw hcap hInitial
  have hTwo2:run 2 (v,w)=some (x,y):=by
    simpa only [x,y] using hTwo
  have hThirdGuard:2*x+3≤y:=by dsimp [x,y];omega
  have hThird:next (x,y)=some (q,r):=by
    dsimp [q,r]
    simp [next,hThirdGuard]
  have hFourthGuard:2*q+3≤r:=by dsimp [q,r,x,y];omega
  have hFourth:next (q,r)=some (a,b):=by
    dsimp [a,b]
    simp [next,hFourthGuard]
  have hSecond2:run 2 (x,y)=some (a,b):=by
    change (next (x,y)).bind next=some (a,b)
    rw [hThird]
    simpa only [Option.bind_some] using hFourth
  have hFour:run 4 (v,w)=some (a,b):=by
    rw [show 4=2+2 by decide,BB429.run_add,hTwo2]
    simpa only [Option.bind_some] using hSecond2
  have hA:a=(8*v+49)-4*w:=by dsimp[a,q,x];omega
  have hB:b=9*w-14*v-82:=by dsimp[b,r,q,x,y];omega
  simpa only [hA,hB] using hFour

/-- Six-step reset to U0 after the high second first-branch event. -/
theorem odd_V_third_reset (v w:Nat) (hv:v%4=1) (hw:w%4=1)
    (hcap:w+7≤2*v)
    (hfirst:6*v+33≤5*w)
    (hsecond:14*v+82≤9*w)
    (hthird:35*w≤58*v+345):
    run 6 (v,w)=some (0,2*v+w+33) := by
  let a:=(8*v+49)-4*w
  let b:=9*w-14*v-82
  have hFour:=odd_V_two_first v w hv hw hcap hfirst hsecond
  have hAodd:a%2=1:=by dsimp [a];omega
  have hAlarge:3≤a:=by dsimp [a];omega
  have hBmod:b%4=1:=by dsimp [b];omega
  have hBguard:3*b≤2*a+1:=by dsimp [a,b];omega
  have h2:=BB429OddExtension.odd_odd_two_step a b hAodd hAlarge hBmod hBguard
  have hW:2*a+b+17=2*v+w+33:=by dsimp [a,b];omega
  rw [show 6=4+2 by decide, BB429.run_add,hFour]
  simpa only [Option.bind_some,hW] using h2

/-- Full finite transfer to the (k+3)th U-ray under explicit demand guard. -/
theorem odd_V_third_to_U (k w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hcap:w+7≤2*rayV k)
    (hfirst:6*rayV k+33≤5*w)
    (hsecond:14*rayV k+82≤9*w)
    (hthird:35*w≤58*rayV k+345)
    (hdb:rayDemand (k+3)≤2*rayV k+w+33):
    run (k+9) (rayV k,w)=
      some (rayU (k+3),(2*rayV k+w+33)-rayDemand (k+3)) := by
  have hv4:rayV k%4=1:=V_mod k hk
  have h6:=odd_V_third_reset (rayV k) w hv4 hw hcap hfirst hsecond hthird
  have hR:=ray_run (k+3) (2*rayV k+w+33) hdb
  rw [show k+9=6+(k+3) by omega,BB429.run_add,h6]
  simpa only [Option.bind_some] using hR

/-- This branch is encountered at real blank macro step 322. -/
theorem rooted_to_U8_162 : run 336 (0,0)=some (rayU 8,162) := by
  have h0:=BB429OddVHigh.rooted_to_V5_745
  have ht:=odd_V_third_to_U 5 745 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have h14:run 14 (rayV 5,745)=some (rayU 8,162):=by
    simpa only [show 5+9=14 by decide,
      show rayV 5=445 by decide,
      show rayU 8=765 by decide,
      show rayDemand 8=1506 by decide,
      show 2*445+745+33-1506=162 by decide] using ht
  rw [show 336=322+14 by decide,BB429.run_add,h0]
  simpa only [Option.bind_some] using h14

#print axioms odd_V_two_first
#print axioms odd_V_third_reset
#print axioms odd_V_third_to_U
#print axioms rooted_to_U8_162
end BB429OddVThirdOverflow
