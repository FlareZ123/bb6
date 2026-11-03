import ReturnLadder
import EscapeRay
import Lean.Elab.Tactic.Omega

/-!
Parameter-uniform sector transfer for authentic #429 arithmetic highLevelNext
(as source-transcribed by Agent5). The regular U-even corridor endpoint
advances to a genuine V-even corridor. This is a conditional theorem about
synthetic states, not a resolution of the blank-start machine.
-/
namespace BB429ExitTransfer
open BB429 BB429Ladder BB429ElevenExtension

theorem U_mod (k:Nat) (hk:2≤k):rayU k%4=1 := by
  cases k with
  | zero => omega
  | succ j =>
    cases j with
    | zero => omega
    | succ n =>simp only [rayU];omega

theorem U_linear (n : Nat) (hn : 4 ≤ n) : 6*n+20 ≤ rayU n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : 4≤n
    · have hh := ih hn4
      simp only [rayU]
      omega
    · have heq:n=3:=by omega
      subst n
      decide

theorem U3_ge_V (l:Nat):rayV l ≤ rayU (l+3):=by
  induction l with
  | zero => decide
  | succ l ih =>
    have heq: l+1+3=(l+3)+1:=by omega
    rw [heq]
    change 2*rayV l+3 ≤ 2*rayU (l+3)+3
    omega

theorem V_margin (l:Nat) (hl:4≤l):
  2*rayU (l+3)+6*l+56 ≤ 4*rayV l := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hp : 4≤l
    · have hh := ih hp
      have heq:l+1+3=(l+3)+1:=by omega
      rw [heq]
      change 2*(2*rayU (l+3)+3)+6*(l+1)+56 ≤ 4*(2*rayV l+3)
      omega
    · have heq:l=3:=by omega
      subst l
      decide

theorem U_strong (l:Nat) (hl:4≤l):18*l+126 ≤ 2*rayU (l+3):=by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hp:4≤l
    · have hh:=ih hp
      have heq:l+1+3=(l+3)+1:=by omega
      rw [heq]
      change 18*(l+1)+126 ≤ 2*(2*rayU (l+3)+3)
      omega
    · have hh:l=3:=by omega
      subst l
      decide

theorem V_margin_strong (l:Nat) (hl:4≤l):
  2*rayU (l+3)+9*l+82 ≤ 4*rayV l := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hp:4≤l
    · have hh:=ih hp
      have heq:l+1+3=(l+3)+1:=by omega
      rw [heq]
      change 2*(2*rayU (l+3)+3)+9*(l+1)+82 ≤ 4*(2*rayV l+3)
      omega
    · have hh:l=3:=by omega
      subst l
      decide

theorem typical_U_to_U (k w r z:Nat)
  (hk:6≤k) (hmod:k%4=2) (hwm:w%4=0)
  (hrm:r%4=2) (heq:w+r+4=2*rayU k)
  (hr:r≤3*k+2) (hz:z+r=3*k+3):
  run (k+2) (rayU k,w)=some (rayU (k+1),z) := by
  have hu : rayU k%4=1 := U_mod k (by omega)
  have hw: w%2=0:=by omega
  have hlt:w<2*rayU k:=by omega
  have hd:3≤rayU k-w/2:=by omega
  have hodd:(rayU k-w/2)%2=1:=by omega
  have hreset:=BB429Ladder.reset_odd_even (rayU k) w hw hlt hd hodd
  have hdemand:=ray_balance (k+1)
  have heqray : rayU (k+1) =2*rayU k+3 := by rfl
  have hbound:rayDemand (k+1)≤2*rayU k+w+10:=by omega
  have hrun:=ray_run (k+1) (2*rayU k+w+10) hbound
  have hsub:2*rayU k+w+10-rayDemand (k+1)=z:=by omega
  have htime:k+2=1+(k+1):=by omega
  have hfirst:run 1 (rayU k,w)=some (0,2*rayU k+w+10):=hreset
  rw [htime, BB429Escape.run_add,hfirst]
  simp only [Option.bind_some]
  simpa only [hsub] using hrun

theorem U_to_V (l u z:Nat) (hu:u=rayU (l+3))
  (hl:4≤l) (hlm:l%4=0) (hz:z%4=3) (hzbd:z≤6*l+47):
  run (l+2) (u,z) =
    some (rayV l,(2*u+z+9)-demandV l) := by
  have hh:u%2=1:=by rw [hu];have h:=U_mod (l+3) (by omega);omega
  have hu11:11≤u:=by rw [hu];have h:=U_linear (l+3) (by omega);omega
  have hh2:3*z≤2*u+15:=by
    have he:=U_strong l hl
    rw [hu]
    omega
  have htwo:=BB429ElevenOddExtension.odd_even_two_step u z hh hu11 hz hh2
  have hge:=U3_ge_V l
  have hvbal:=v_balance l
  have hvbd:demandV l≤2*u+z+9:=by rw [hu];omega
  have hrun:=v_run l (2*u+z+9) hvbd
  have htime:l+2=2+l:=by omega
  rw [htime, BB429Escape.run_add,htwo]
  simpa only [Option.bind_some] using hrun

theorem typical_U_to_V (k w r z:Nat)
  (hk:6≤k) (hmod:k%4=2) (hwm:w%4=0)
  (hrm:r%4=2) (heq:w+r+4=2*rayU k)
  (hr:r≤3*k+2) (hz:z+r=3*k+3):
  run (2*k+2) (rayU k,w) =
    some (rayV (k-2),(2*rayU (k+1)+z+9)-demandV (k-2)) := by
  have hl:k-2+3=k+1:=by omega
  have htime:2*k+2=(k+2)+((k-2)+2):=by omega
  have hu:= typical_U_to_U k w r z hk hmod hwm hrm heq hr hz
  have hzmod:z%4=3:=by omega
  have hzb:z≤6*(k-2)+47:=by omega
  have hv:=U_to_V (k-2) (rayU (k+1)) z (by rw [hl]) (by omega) (by omega) hzmod hzb
  rw [htime,BB429Escape.run_add,hu]
  simpa only [Option.bind_some] using hv

theorem V_mod (l:Nat) (hl:1≤l):rayV l%4=1:=by
  cases l with
  | zero => omega
  | succ j =>
    have hj:=vU_odd j
    simp only [rayV]
    omega

/-- Every regular U-even corridor endpoint reaches a guarded V-even corridor. -/
theorem typical_U_to_V_even (k w r z:Nat)
  (hk:6≤k) (hmod:k%4=2) (hwm:w%4=0)
  (hrm:r%4=2) (heq:w+r+4=2*rayU k)
  (hr:r≤3*k+2) (hz:z+r=3*k+3):
  ∃ y:Nat,
    run (2*k+2) (rayU k,w) = some (rayV (k-2),y) ∧
    y%4=2 ∧ y+4≤2*rayV (k-2) := by
  let l:=k-2
  let u:=rayU (k+1)
  let v:=rayV l
  let W:=2*u+z+9
  let y:=W-demandV l
  have hl:l+3=k+1:=by dsimp [l];omega
  have hm:l%4=0:=by dsimp [l];omega
  have hlu:4≤l:=by dsimp [l];omega
  have hvmod:v%4=1:=V_mod l (by omega)
  have humod:u%4=1:=by dsimp [u];exact U_mod (k+1) (by omega)
  have hzmod:z%4=3:=by omega
  have hzb:z≤3*l+7:=by dsimp [l];omega
  have hge: v≤u:=by dsimp [u,v];rw [←hl];exact U3_ge_V l
  have hbalance:=v_balance l
  have hmargin:=V_margin_strong l hlu
  have hmarginUV:2*u+9*l+82≤4*v:=by
    change 2*rayU (k+1)+9*l+82≤4*rayV l
    rw [←hl]
    exact hmargin
  have hdb:demandV l≤W:=by dsimp [W];omega
  have hy:y+demandV l=W:=by dsimp [y];omega
  have heven:y%4=2:=by dsimp [W,u,v] at hy;omega
  have hguard:y+4≤2*v:=by
    omega
  refine ⟨y, ?_, heven, hguard⟩
  simpa only [y,W,u,v,l] using typical_U_to_V k w r z hk hmod hwm hrm heq hr hz

#print axioms typical_U_to_V_even
#print axioms typical_U_to_U
#print axioms U_to_V
#print axioms typical_U_to_V
end BB429ExitTransfer
