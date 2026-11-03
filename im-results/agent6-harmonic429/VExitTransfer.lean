import CorridorExceptions
import Lean.Elab.Tactic.Omega

/-!
Exact regular and exceptional V-even corridor-end transfers for BB429's
source-transcribed map. Assumes neither global nonhalting nor blank reachability.
-/
namespace BB429VExitTransfer
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer BB429CorridorExceptions

theorem V_mod (l:Nat) (hl:1≤l) : rayV l%4=1:=BB429ExitTransfer.V_mod l hl

theorem V_boundary_reset (l w r:Nat)
  (hl:4≤l) (hm:l%4=0) (hw:w%4=2)
  (hrm:r%4=0) (heq:w+r+4=2*rayV l):
  run 1 (rayV l,w)=some (11,2*rayV l+w-2) := by
  have hvmod:rayV l%2=1:=vU_odd l
  have hguard:w+4≤2*rayV l:=by omega
  exact BB429ElevenExtension.reset_even2 (rayV l) w hvmod hw hguard

theorem V_regular_to_next (l w r z:Nat)
  (hl:4≤l) (hm:l%4=0) (hw:w%4=2)
  (hrm:r%4=0) (heq:w+r+4=2*rayV l)
  (hr:r≤3*l+12) (hz:z+r=3*l+13):
  run (l+2) (rayV l,w)=some (rayV (l+1),z) := by
  have hfirst:=V_boundary_reset l w r hl hm hw hrm heq
  have hbal:=v_balance (l+1)
  have hnext:rayV (l+1)=2*rayV l+3:=by rfl
  have hdb:demandV (l+1)≤2*rayV l+w-2:=by omega
  have hray:=v_run (l+1) (2*rayV l+w-2) hdb
  have hsub:(2*rayV l+w-2)-demandV (l+1)=z:=by omega
  rw [show l+2=1+(l+1) by omega,BB429.run_add,hfirst]
  simpa only [Option.bind_some,hsub] using hray

theorem V_exception_first (l w r:Nat)
  (hl:4≤l) (hm:l%4=0) (hw:w%4=2)
  (hrm:r%4=0) (heq:w+r+4=2*rayV l)
  (hr:r=3*l+16):
  run (l+1) (rayV l,w)=some (rayV l,2*rayV l) := by
  have hfirst:=V_boundary_reset l w r hl hm hw hrm heq
  have hbal:=v_balance l
  have hdb:demandV l≤2*rayV l+w-2:=by omega
  have hray:=v_run l (2*rayV l+w-2) hdb
  have hsub:(2*rayV l+w-2)-demandV l=2*rayV l:=by omega
  rw [show l+1=1+l by omega,BB429.run_add,hfirst]
  simpa only [Option.bind_some,hsub] using hray

theorem V_U_lower (l:Nat) (hl:4≤l):
    12*rayV l+9*l+48 ≤ 8*rayU (l+3):=by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hp:4≤l
    · have h:=ih hp
      have heq:l+1+3=(l+3)+1:=by omega
      rw [heq]
      change 12*(2*rayV l+3)+9*(l+1)+48 ≤ 8*(2*rayU (l+3)+3)
      omega
    · have h:l=3:=by omega
      subst l
      decide

theorem V_exception_middle (l:Nat) (hl:4≤l) (hm:l%4=0):
  run (2*l+7) (rayV l,2*rayV l)=
    some (rayV (l+1),6*l+49) := by
  let v:=rayV l
  let j:=l+3
  let u:=rayU j
  let W0:=4*v+12
  let zU:=W0-rayDemand j
  let W11:=2*u+zU+9
  have hUmod:u%4=1:=by dsimp [u,j];exact U_mod (l+3) (by omega)
  have hjmod:j%4=3:=by dsimp [j];omega
  have hUMargin:=V_margin_strong l hl
  have hUlower:=V_U_lower l hl
  have hDbal:=ray_balance j
  have hW0:rayDemand j≤W0:=by dsimp [j,u,W0,v] at *;omega
  have hZ:zU+rayDemand j=W0:=by dsimp [zU];omega
  have hZmod:zU%4=3:=by dsimp [W0] at hZ;omega
  have hZbound:3*zU≤2*u+15:=by
    dsimp [W0,v] at hZ
    dsimp [j,u] at *
    omega
  have hUlarge:11≤u:=by
    have h:=U_linear j (by dsimp [j];omega)
    dsimp [u]
    omega
  have huodd:u%2=1:=by omega
  have hfirst:run 1 (rayV l,2*rayV l)=some (0,W0):=by
    change next (rayV l,2*rayV l)=some (0,W0)
    dsimp [W0,v]
    simp [next]
  have hUrun:=ray_run j W0 hW0
  have hStep:run 2 (u,zU)=some (11,W11):=
    BB429ElevenOddExtension.odd_even_two_step u zU huodd hUlarge hZmod hZbound
  have hVbal:=v_balance (l+1)
  have hVnext:rayV (l+1)=2*v+3:=by rfl
  have hVdb:demandV (l+1)≤W11:=by
    dsimp [W11] at *
    omega
  have hVrun:=v_run (l+1) W11 hVdb
  have hVsub:W11-demandV (l+1)=6*l+49:=by omega
  have hViaU:run (l+4) (rayV l,2*rayV l)=some (u,zU):=by
    rw [show l+4=1+j by dsimp [j];omega,BB429.run_add,hfirst]
    simpa only [Option.bind_some,u,zU] using hUrun
  have hViaV:run (l+3) (u,zU)=some (rayV (l+1),6*l+49):=by
    rw [show l+3=2+(l+1) by omega,BB429.run_add,hStep]
    simpa only [Option.bind_some,hVsub] using hVrun
  rw [show 2*l+7=(l+4)+(l+3) by omega,BB429.run_add,hViaU]
  simpa only [Option.bind_some] using hViaV

theorem V_exception_to_next (l w r:Nat)
  (hl:4≤l) (hm:l%4=0) (hw:w%4=2)
  (hrm:r%4=0) (heq:w+r+4=2*rayV l)
  (hr:r=3*l+16):
  run (3*l+8) (rayV l,w)=some (rayV (l+1),6*l+49) := by
  have hfirst:=V_exception_first l w r hl hm hw hrm heq hr
  have hrest:=V_exception_middle l hl hm
  rw [show 3*l+8=(l+1)+(2*l+7) by omega,BB429.run_add,hfirst]
  simpa only [Option.bind_some] using hrest

/-- Complete transfer to next V ray, all possible corridor-end residues. -/
theorem V_even_complete_transfer (l w r:Nat)
  (hl:4≤l) (hm:l%4=0) (hw:w%4=2)
  (hrm:r%4=0) (heq:w+r+4=2*rayV l)
  (hr:r<3*l+20):
  ∃ n z:Nat, (n=l+2 ∨ n=3*l+8) ∧
    run n (rayV l,w)=some (rayV (l+1),z) ∧ z%4=1 := by
  have hcases:r≤3*l+12 ∨ r=3*l+16:=by omega
  rcases hcases with ht | hx
  · let z:=3*l+13-r
    have he:z+r=3*l+13:=by dsimp [z];omega
    have hmz:z%4=1:=by omega
    exact ⟨l+2,z,Or.inl rfl,V_regular_to_next l w r z hl hm hw hrm heq ht he,hmz⟩
  · have hh:=V_exception_to_next l w r hl hm hw hrm heq hx
    refine ⟨3*l+8,6*l+49,Or.inr rfl,hh,?_⟩
    omega

#print axioms V_exception_middle
#print axioms V_even_complete_transfer
#print axioms V_regular_to_next
#print axioms V_exception_first
end BB429VExitTransfer
