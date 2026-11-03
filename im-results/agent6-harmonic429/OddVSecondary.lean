import OddCascade
import Lean.Elab.Tactic.Omega

/-!
A conditional second overflow of the odd-V-one sector. The first two
odd-one transitions feed an odd-even two-step overflow; when its output
satisfies the odd-odd reset guard, a root-zero U-ray is reached.

This is a parameter-uniform accelerated transition grammar, with a genuine
blank-origin entry at macro 275. No statement about eventual blank halting
or nonhalting is made.
-/
namespace BB429OddVSecondary
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

/-- Exact four-step double overflow of V_k, k congruent to one mod four. -/
theorem odd_V_double_overflow (k w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hcap:w+7≤2*rayV k)
    (hscap:5*w≤6*rayV k+23)
    (hsecond:10*rayV k+73≤11*w):
    run 4 (rayV k,w)=
      some ((6*rayV k+48)-5*w,11*w-10*rayV k-72) := by
  let v:=rayV k
  let x:=2*v-w+10
  let y:=3*w-2*v-10
  have hv4:v%4=1:=by dsimp[v];exact V_mod k hk
  have hvodd:v%2=1:=by omega
  have hfirstover:2*v+13≤3*w:=by dsimp [v] at *;omega
  have hFirst:=BB429OddCascade.odd_one_overflow_two_step v w hvodd
    hw hcap hfirstover
  have hxodd:x%2=1:=by dsimp [x];omega
  have hxlarge:11≤x:=by dsimp [x];omega
  have hy3:y%4=3:=by dsimp [y];omega
  have hcap2:y+7≤2*x:=by dsimp [x,y,v] at *;omega
  have hover2:2*x+22≤3*y:=by dsimp [x,y,v] at *;omega
  have hSecond:=BB429OddBoundary.overflow_two_step x y hxlarge hxodd
    hy3 hcap2 hover2
  have hX:2*x-y+18=(6*v+48)-5*w:=by dsimp[x,y];omega
  have hY:3*y-2*x-22=11*w-10*v-72:=by dsimp[x,y];omega
  have hFirst2:run 2 (v,w)=some (x,y):=by
    simpa only [v,x,y] using hFirst
  rw [show 4=2+2 by decide,BB429.run_add,hFirst2]
  simpa only [Option.bind_some,v,hX,hY] using hSecond

/-- Conditional six-step reset back to the root-zero branch. -/
theorem odd_V_to_U_zero (k w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hcap:w+7≤2*rayV k)
    (hscap:5*w≤6*rayV k+23)
    (hsecond:10*rayV k+73≤11*w)
    (hreset:43*w≤42*rayV k+313):
    run 6 (rayV k,w)=some (0,2*rayV k+w+41) := by
  let v:=rayV k
  let a:=(6*v+48)-5*w
  let b:=11*w-10*v-72
  have hv4:v%4=1:=by dsimp[v];exact V_mod k hk
  have haodd:a%2=1:=by dsimp[a];omega
  have halarge:3≤a:=by dsimp[a];omega
  have hbmod:b%4=1:=by dsimp[b];omega
  have hguard:3*b≤2*a+1:=by dsimp[a,b,v] at *;omega
  have hFour:run 4 (v,w)=some (a,b):=by
    simpa only [v,a,b] using
      odd_V_double_overflow k w hk hkm hw hcap hscap hsecond
  have hSecond:=BB429OddExtension.odd_odd_two_step a b haodd
    halarge hbmod hguard
  have hW:2*a+b+17=2*v+w+41:=by dsimp[a,b];omega
  rw [show 6=4+2 by decide,BB429.run_add,hFour]
  simpa only [Option.bind_some,v,hW] using hSecond

/-- Transfer the reset through the entire U_(k+2) first-branch ray. -/
theorem odd_V_to_U_ray (k w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hcap:w+7≤2*rayV k)
    (hscap:5*w≤6*rayV k+23)
    (hsecond:10*rayV k+73≤11*w)
    (hreset:43*w≤42*rayV k+313):
    run (k+8) (rayV k,w)=some
      (rayU (k+2),(2*rayV k+w+41)-rayDemand (k+2)) := by
  have horder:rayU (k+2)≤rayV k:=by
    have h:=BB429CrossRayReturn.cross_ray_order (k-1)
    have h1:(k-1)+1=k:=by omega
    have h2:(k-1)+3=k+2:=by omega
    simpa only [h1,h2] using h
  have hbal:=ray_balance (k+2)
  have hdb:rayDemand (k+2)≤2*rayV k+w+41:=by omega
  have hzero:=odd_V_to_U_zero k w hk hkm hw hcap hscap hsecond hreset
  have hR:=ray_run (k+2) (2*rayV k+w+41) hdb
  rw [show k+8=6+(k+2) by omega,BB429.run_add,hzero]
  simpa only [Option.bind_some] using hR

/-- The blank-origin orbit uses this second overflow at the next V5 gate. -/
theorem rooted_to_U7_615 : run 275 (0,0)=some (rayU 7,615) := by
  have h0:=BB429OddCascade.rooted_to_V5_425
  have ht:=odd_V_to_U_ray 5 425 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hV5:rayV 5=445:=by decide
  have hU7:rayU 7=381:=by decide
  have hD7:rayDemand 7=741:=by decide
  have h13:run 13 (rayV 5,425)=some (rayU 7,615):=by
    simpa only [show 5+8=13 by decide,hV5,hU7,hD7,
      show 2*445+425+41-741=615 by decide] using ht
  rw [show 275=262+13 by decide,BB429.run_add,h0]
  simpa only [Option.bind_some] using h13

#print axioms odd_V_double_overflow
#print axioms odd_V_to_U_zero
#print axioms odd_V_to_U_ray
#print axioms rooted_to_U7_615
end BB429OddVSecondary
