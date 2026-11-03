import OddVSecondary
import Lean.Elab.Tactic.Omega

/-!
The high odd-one sector of BB429's V-ray has a third conditional affine
return. It consists of a two-step odd-one overflow, a first branch, a
single even reset to V0, then k first-branch moves to the same V_k.

The genuine blank orbit performs four such returns at k=5.
-/
namespace BB429OddVHigh
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

/-- High odd-one V-sector return with increment 3k+33. -/
theorem odd_V_high_bounce (k w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hcap:w+7≤2*rayV k)
    (hhigh:6*rayV k+33≤5*w)
    (hlimit:9*w≤14*rayV k+75):
    run (k+4) (rayV k,w)=some (rayV k,w+3*k+33) := by
  let v:=rayV k
  let x:=2*v-w+10
  let y:=3*w-2*v-10
  let a:=2*x+3
  let b:=y-2*x-3
  have hv4:v%4=1:=by dsimp [v];exact V_mod k hk
  have hvodd:v%2=1:=by omega
  have hfirstover:2*v+13≤3*w:=by dsimp[v] at *;omega
  have hTwo:=BB429OddCascade.odd_one_overflow_two_step v w hvodd hw
    hcap hfirstover
  have hTwo2:run 2 (v,w)=some (x,y):=by
    simpa only [x,y] using hTwo
  have hFGuard:2*x+3≤y:=by dsimp [x,y,v] at *;omega
  have hF:next (x,y)=some (a,b):=by
    dsimp [a,b]
    unfold next
    simp [hFGuard]
  have hAm:a%2=1:=by dsimp [a];omega
  have hBmod:b%4=2:=by dsimp [b,x,y];omega
  have hCapB:b+4≤2*a:=by dsimp [a,b,x,y,v] at *;omega
  have hReset:=BB429ElevenExtension.reset_even2 a b hAm hBmod hCapB
  have hThree:run 3 (v,w)=some (a,b):=by
    rw [show 3=2+1 by decide,BB429.run_add,hTwo2]
    change (next (x,y)) = some (a,b)
    exact hF
  have hFour:run 4 (v,w)=some (11,2*a+b-2):=by
    rw [show 4=3+1 by decide,BB429.run_add,hThree]
    change next (a,b)=some (11,2*a+b-2)
    exact hReset
  have hW:2*a+b-2=2*v+w+11:=by dsimp[a,b,x,y];omega
  have hFour':run 4 (v,w)=some (11,2*v+w+11):=by
    simpa only [hW] using hFour
  have hBal:=v_balance k
  have hdb:demandV k≤2*v+w+11:=by dsimp[v] at *;omega
  have hR:=v_run k (2*v+w+11) hdb
  have hFinal:(2*v+w+11)-demandV k=w+3*k+33:=by dsimp[v] at *;omega
  rw [show k+4=4+k by omega,BB429.run_add,hFour']
  simpa only [Option.bind_some,v,hFinal] using hR

/-- Arbitrary finite repetitions of the high V-odd-one return,
with guards checked at the final represented counter. -/
theorem odd_V_high_ladder (k n w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hhigh:6*rayV k+33≤5*w)
    (hbound:w+n*(3*k+33)+7≤2*rayV k)
    (hlimit:9*(w+n*(3*k+33))≤14*rayV k+75):
    run (n*(k+4)) (rayV k,w)=some (rayV k,w+n*(3*k+33)) := by
  have hdmod:(3*k+33)%4=0:=by omega
  induction n with
  | zero => simp [BB429.run]
  | succ n ih =>
    have hboundN:w+n*(3*k+33)+7≤2*rayV k:=by
      rw [Nat.succ_mul n (3*k+33)] at hbound
      omega
    have hlimitN:9*(w+n*(3*k+33))≤14*rayV k+75:=by
      rw [Nat.succ_mul n (3*k+33)] at hlimit
      omega
    have hwmN:(w+n*(3*k+33))%4=1:=by
      simp [Nat.add_mod,Nat.mul_mod,hw,hdmod]
    have hhighN:6*rayV k+33≤5*(w+n*(3*k+33)):=by omega
    have hStep:=odd_V_high_bounce k (w+n*(3*k+33)) hk hkm
      hwmN hboundN hhighN hlimitN
    rw [Nat.succ_mul,BB429.run_add,ih hboundN hlimitN]
    simp only [Option.bind_some,hStep]
    have hEq:w+n*(3*k+33)+3*k+33=w+(n+1)*(3*k+33):=by
      rw [Nat.succ_mul n (3*k+33)]
      omega
    exact congrArg (fun z:Nat=>some (rayV k,z)) hEq

/-- A short exact computational bridge to the first high V5 return. -/
theorem rooted_to_V5_553 : run 286 (0,0)=some (rayV 5,553) := by
  have h0:=BB429OddCascade.rooted_to_V5_425
  have hV5:rayV 5=445:=by decide
  have h24:run 24 (rayV 5,425)=some (rayV 5,553):=by
    rw [hV5]
    decide
  rw [show 286=262+24 by decide,BB429.run_add,h0]
  simpa only [Option.bind_some] using h24

/-- Four genuine high V5 returns raise w by 4*48. -/
theorem rooted_to_V5_745 : run 322 (0,0)=some (rayV 5,745) := by
  have h0:=rooted_to_V5_553
  have hA:=odd_V_high_bounce 5 553 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hB:=odd_V_high_bounce 5 601 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hC:=odd_V_high_bounce 5 649 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hD:=odd_V_high_bounce 5 697 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have h9a:run 9 (rayV 5,553)=some (rayV 5,601):=by
    simpa only [show 5+4=9 by decide,
      show 553+3*5+33=601 by decide] using hA
  have h9b:run 9 (rayV 5,601)=some (rayV 5,649):=by
    simpa only [show 5+4=9 by decide,
      show 601+3*5+33=649 by decide] using hB
  have h9c:run 9 (rayV 5,649)=some (rayV 5,697):=by
    simpa only [show 5+4=9 by decide,
      show 649+3*5+33=697 by decide] using hC
  have h9d:run 9 (rayV 5,697)=some (rayV 5,745):=by
    simpa only [show 5+4=9 by decide,
      show 697+3*5+33=745 by decide] using hD
  have h36:run 36 (rayV 5,553)=some (rayV 5,745):=by
    rw [show 36=9+27 by decide,BB429.run_add,h9a]
    simp only [Option.bind_some]
    rw [show 27=9+18 by decide,BB429.run_add,h9b]
    simp only [Option.bind_some]
    rw [show 18=9+9 by decide,BB429.run_add,h9c]
    simpa only [Option.bind_some] using h9d
  rw [show 322=286+36 by decide,BB429.run_add,h0]
  simpa only [Option.bind_some] using h36

#print axioms odd_V_high_bounce
#print axioms odd_V_high_ladder
#print axioms rooted_to_V5_745
end BB429OddVHigh
