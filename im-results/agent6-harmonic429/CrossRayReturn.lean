import VWholeCorridor
import Lean.Elab.Tactic.Omega

/-!
A fifth accelerated corridor family: an exact alternating cross-ray word
between V_(l+1), U_(l+3), and back to V_(l+1). The parameter-uniform
induction gives a finite admissible-word ladder. It does not decide BB429.
-/
namespace BB429CrossRayReturn
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer BB429VExitTransfer

theorem cross_ray_order (l:Nat):rayU (l+3)≤rayV (l+1):=by
  induction l with
  | zero => decide
  | succ l ih =>
    have h1:l+1+3=(l+3)+1:=by omega
    have h2:l+1+1=(l+1)+1:=by omega
    rw [h1,h2]
    change 2*rayU (l+3)+3≤2*rayV (l+1)+3
    omega

theorem cross_ray_return (l w:Nat) (hl:4≤l) (hm:l%4=0)
    (hw:w%4=1)
    (hguard:3*w+6*rayV (l+1)+9*(l+3)+36≤8*rayU (l+3)):
    run (2*l+8) (rayV (l+1),w)=
      some (rayV (l+1),w+6*l+60) := by
  let i:=l+1
  let j:=l+3
  let v:=rayV i
  let u:=rayU j
  let W0:=2*v+w+17
  let zU:=W0-rayDemand j
  let W11:=2*u+zU+9
  have horder:v≥u:=by dsimp [u,v,i,j];exact cross_ray_order l
  have hVmod:v%4=1:=by dsimp [v,i];exact BB429ExitTransfer.V_mod (l+1) (by omega)
  have hUmod:u%4=1:=by dsimp [u,j];exact U_mod (l+3) (by omega)
  have hjmod:j%4=3:=by dsimp [j];omega
  have hvodd:v%2=1:=by omega
  have hUodd:u%2=1:=by omega
  have hvlarge:3≤v:=by
    have hh:=vU_large i
    dsimp [v]
    omega
  have hularge:11≤u:=by
    have hh:=U_linear j (by dsimp [j];omega)
    dsimp [u]
    omega
  have hguardV:3*w≤2*v+1:=by dsimp [u,v,i,j] at *;omega
  have hVtwo:=BB429OddExtension.odd_odd_two_step v w hvodd hvlarge hw hguardV
  have hUbal:=ray_balance j
  have hdbU:rayDemand j≤W0:=by dsimp [W0];omega
  have hZ:zU+rayDemand j=W0:=by dsimp [zU];omega
  have hZmod:zU%4=3:=by dsimp [W0] at hZ;omega
  have hUguard:3*zU≤2*u+15:=by
    dsimp [u,v,i,j,W0] at *
    omega
  have hUrun:=ray_run j W0 hdbU
  have hUtwo:=BB429ElevenOddExtension.odd_even_two_step u zU hUodd hularge hZmod hUguard
  have hVbal:=v_balance i
  have hdbV:demandV i≤W11:=by dsimp [W11,W0] at *;omega
  have hVrun:=v_run i W11 hdbV
  have hZout:W11-demandV i=w+6*l+60:=by
    dsimp [i,j,v,u,W0,W11] at *
    omega
  have hfirst:run (j+2) (v,w)=some (u,zU):=by
    rw [show j+2=2+j by omega,BB429.run_add,hVtwo]
    simpa only [Option.bind_some,u,zU] using hUrun
  have hsecond:run (i+2) (u,zU)=some (v,w+6*l+60):=by
    rw [show i+2=2+i by omega,BB429.run_add,hUtwo]
    simpa only [Option.bind_some,v,hZout] using hVrun
  have htime:2*l+8=(j+2)+(i+2):=by dsimp [j,i];omega
  rw [htime,BB429.run_add,hfirst]
  simpa only [Option.bind_some,v] using hsecond

/-- An arbitrary finite repetition count is certified under the last guard. -/
theorem cross_ray_ladder (l n w:Nat) (hl:4≤l) (hm:l%4=0)
    (hw:w%4=1)
    (hb:3*(w+n*(6*l+60))+6*rayV (l+1)+9*(l+3)+36≤8*rayU (l+3)):
    run (n*(2*l+8)) (rayV (l+1),w)=
      some (rayV (l+1),w+n*(6*l+60)) := by
  have hdelta:(6*l+60)%4=0:=by omega
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hbn:3*(w+n*(6*l+60))+6*rayV (l+1)+9*(l+3)+36≤8*rayU (l+3):=by
      have hmul:(n+1)*(6*l+60)=n*(6*l+60)+(6*l+60):=by
        rw [show n+1=Nat.succ n by omega,Nat.succ_mul]
      rw [hmul] at hb
      omega
    have hw4:(w+n*(6*l+60))%4=1:=by
      simp [Nat.add_mod,Nat.mul_mod,hw,hdelta]
    have hr:=cross_ray_return l (w+n*(6*l+60)) hl hm hw4 hbn
    rw [Nat.succ_mul,BB429.run_add,ih hbn]
    simp only [Option.bind_some,hr]
    have heq:w+n*(6*l+60)+6*l+60=w+(n+1)*(6*l+60):=by
      rw [Nat.succ_mul n (6*l+60)]
      omega
    exact congrArg (fun z:Nat=>some (rayV (l+1),z)) heq

/-- Real blank-entry witness, composed from 186-step source-connected chain. -/
theorem rooted_to_V5_101 : run 202 (0,0)=some (rayV 5,101) := by
  have h0:=BB429VWholeCorridor.rooted_to_V5_17
  have h1:=cross_ray_return 4 17 (by decide) (by decide) (by decide) (by decide)
  rw [show 202=186+16 by decide,BB429.run_add,h0]
  simpa only [Option.bind_some,show 2*4+8=16 by decide,
    show 17+6*4+60=101 by decide] using h1

#print axioms cross_ray_return
#print axioms cross_ray_ladder
#print axioms rooted_to_V5_101
end BB429CrossRayReturn
