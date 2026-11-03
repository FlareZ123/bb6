import OddVThirdOverflow
import Lean.Elab.Tactic.Omega

/-!
A new complete conditional odd V-high return word. In the overflow
sector the machine reaches root zero, traverses a longer U_(k+3) ray,
resets even into the V0 origin, and traverses V_k back to its source
cross-section. The total macro time is 2k+10, increment 6k+62.

This is a rigorous bounded finite return under explicit original-state
guards. It does not alone prove that the blank-root orbit never halts.
-/
namespace BB429OddVHighReturn
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

/-- Uniform separation sufficient for the U-to-V reset cap. -/
theorem v_u_margin (k:Nat) (hk:1≤k) :
    4*rayV k+30+3*(k+3)≤4*rayU (k+3) := by
  obtain ⟨n,hn⟩:∃n,k=n+1:=⟨k-1,by omega⟩
  subst k
  induction n with
  | zero => decide
  | succ n ih =>
    have hshift:(n+1+1)+3=((n+1)+3)+1:=by omega
    rw [hshift]
    change 4*(2*rayV (n+1)+3)+30+3*(((n+1)+3)+1)≤
      4*(2*rayU ((n+1)+3)+3)
    omega

/-- The overflowing source V sector returns to exactly the same V ray. -/
theorem high_V_overflow_return (k w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hcap:w+7≤2*rayV k)
    (hfirst:6*rayV k+33≤5*w)
    (hsecond:14*rayV k+82≤9*w)
    (hthird:35*w≤58*rayV k+345)
    (hdb:rayDemand (k+3)≤2*rayV k+w+33):
    run (2*k+10) (rayV k,w)=some (rayV k,w+6*k+62) := by
  let j:=k+3
  let v:=rayV k
  let u:=rayU j
  let W:=2*v+w+33
  let z:=W-rayDemand j
  let W1:=2*u+z-2
  have hMargins:=v_u_margin k hk
  have hV4:v%4=1:=by dsimp[v];exact V_mod k hk
  have hU4:u%4=1:=by dsimp[u,j];exact U_mod (k+3) (by omega)
  have hj4:j%4=0:=by dsimp[j];omega
  have hUbal:=ray_balance j
  have hVbal:=v_balance k
  have hDemand:rayDemand j≤W:=by dsimp [j,W,v] at *;exact hdb
  have hZ:z+rayDemand j=W:=by dsimp[z];omega
  have hz4:z%4=2:=by dsimp[W] at hZ;omega
  have hZguard:z+4≤2*u:=by
    dsimp [u,v,j,W] at *
    omega
  have huodd:u%2=1:=by omega
  have hreset:=BB429ElevenExtension.reset_even2 u z huodd hz4 hZguard
  have hVdb:demandV k≤W1:=by
    dsimp[W1,u,v] at *
    omega
  have hVrun:=v_run k W1 hVdb
  have hFinal:W1-demandV k=w+6*k+62:=by
    dsimp[W1,W,u,v,j] at *
    omega
  have hFirst:=BB429OddVThirdOverflow.odd_V_third_to_U k w hk hkm
    hw hcap hfirst hsecond hthird hdb
  have hFirst2:run (k+9) (v,w)=some (u,z):=by
    simpa only [j,v,u,z,W] using hFirst
  have hLast:run (k+1) (u,z)=some (v,w+6*k+62):=by
    rw [show k+1=1+k by omega,BB429.run_add]
    change (next (u,z)).bind (run k)=_
    rw [hreset]
    simpa only [Option.bind_some,W1,hFinal,v] using hVrun
  rw [show 2*k+10=(k+9)+(k+1) by omega,BB429.run_add,hFirst2]
  simpa only [Option.bind_some,v] using hLast

/-- Genuine source-transcribed blank-origin return, macro 322 to 342. -/
theorem rooted_to_V5_837 : run 342 (0,0)=some (rayV 5,837) := by
  have h0:=BB429OddVHigh.rooted_to_V5_745
  have hr:=high_V_overflow_return 5 745
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have h20:run 20 (rayV 5,745)=some (rayV 5,837):=by
    simpa only [show 2*5+10=20 by decide,
      show 745+6*5+62=837 by decide] using hr
  rw [show 342=322+20 by decide,BB429.run_add,h0]
  simpa only [Option.bind_some] using h20

#print axioms v_u_margin
#print axioms high_V_overflow_return
#print axioms rooted_to_V5_837
end BB429OddVHighReturn
