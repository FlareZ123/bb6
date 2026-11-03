import ExitTransfer
import Lean.Elab.Tactic.Omega

/-!
All-parameter completion of the U-even corridor-to-V-even transfer
for BB429's faithful source-transcribed accelerated two-counter map.
The two exceptional residues are included. It is still conditional on
entering the U-even corridor and does not decide the genuine blank machine.
-/
namespace BB429CorridorExceptions
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

theorem U_to_V_good (l u z:Nat)
  (hu:u=rayU (l+3)) (hl:4≤l) (hm:l%4=0)
  (hz:z%4=3) (hzbound:z≤6*l+47):
  ∃ y:Nat,run (l+2) (u,z)=some (rayV l,y) ∧
     y%4=2 ∧ y+4≤2*rayV l := by
  let v:=rayV l
  let W:=2*u+z+9
  let y:=W-demandV l
  have hh:u%4=1:=by rw [hu];exact U_mod (l+3) (by omega)
  have hvmod:v%4=1:=V_mod l (by omega)
  have hbal:=v_balance l
  have hge: v≤u:=by dsimp [v];rw [hu];exact U3_ge_V l
  have hmarginUV:2*u+9*l+82≤4*v:=by
    change 2*u+9*l+82≤4*rayV l
    rw [hu]
    exact V_margin_strong l hl
  have hdb:demandV l≤W:=by dsimp [W];omega
  have hy:y+demandV l=W:=by dsimp [y];omega
  have hy2:y%4=2:=by dsimp [W] at hy;omega
  have hyguard:y+4≤2*v:=by omega
  refine ⟨y, ?_, hy2, hyguard⟩
  simpa only [y,W,v] using U_to_V l u z hu hl hm hz hzbound

theorem boundary_reset (k w r:Nat)
  (hk:6≤k) (hm:k%4=2) (hw:w%4=0)
  (hrm:r%4=2) (heq:w+r+4=2*rayU k):
  run 1 (rayU k,w)=some (0,2*rayU k+w+10) := by
  have hu:rayU k%4=1:=U_mod k (by omega)
  have he:w%2=0:=by omega
  have hlt:w<2*rayU k:=by omega
  have hd:3≤rayU k-w/2:=by omega
  have ho:(rayU k-w/2)%2=1:=by omega
  exact BB429Ladder.reset_odd_even (rayU k) w he hlt hd ho

theorem short_U (k w r a:Nat)
  (hk:6≤k) (hm:k%4=2) (hw:w%4=0) (hrm:r%4=2)
  (heq:w+r+4=2*rayU k) (ha: a+ r=2*rayU k+3*k+6):
  run (k+1) (rayU k,w) = some (rayU k,a) := by
  have hfirst:=boundary_reset k w r hk hm hw hrm heq
  have hbal:=ray_balance k
  have hbound:rayDemand k≤2*rayU k+w+10:=by omega
  have hray:=ray_run k (2*rayU k+w+10) hbound
  have hsub:(2*rayU k+w+10)-rayDemand k=a:=by omega
  rw [show k+1=1+k by omega,BB429Escape.run_add,hfirst]
  simpa only [Option.bind_some,hsub] using hray

theorem near_up_reset (u:Nat) : next (u,2*u+2)=some (0,4*u+18) := by
  simp [next]

theorem near_down_reset (u:Nat) (hu:2≤u) :
  next (u,2*u-2)=some (0,4*u+8) := by
  have h0:¬2*u-2≥2*u+3:=by omega
  have h1:2*u-2≠2*u+2:=by omega
  have h2:2*u-2≠2*u+1:=by omega
  have h3:2*u-2≠2*u:=by omega
  have he:(2*u-2)%2=0:=by omega
  have hd:u-(2*u-2)/2=1:=by omega
  simp [next,h0,h1,h2,h3,he,hd]
  omega

theorem exceptional_high_to_U (k w r:Nat)
  (hk:6≤k) (hm:k%4=2) (hw:w%4=0) (hrm:r%4=2)
  (heq:w+r+4=2*rayU k) (hr:r=3*k+4):
  run (2*k+3) (rayU k,w)=some (rayU (k+1),3*k+15) := by
  have hr1:= short_U k w r (2*rayU k+2) hk hm hw hrm heq (by omega)
  have hr2:run 1 (rayU k,2*rayU k+2)=some (0,4*rayU k+18):=by
    change next (rayU k,2*rayU k+2)=_
    exact near_up_reset (rayU k)
  have hbal:=ray_balance (k+1)
  have h2:rayU (k+1)=2*rayU k+3:=by rfl
  have hd:rayDemand (k+1)≤4*rayU k+18:=by omega
  have hr3:=ray_run (k+1) (4*rayU k+18) hd
  have hs:(4*rayU k+18)-rayDemand (k+1)=3*k+15:=by omega
  have h23:run (k+2) (rayU k,2*rayU k+2)=some (rayU (k+1),3*k+15):=by
    rw [show k+2=1+(k+1) by omega,BB429Escape.run_add,hr2]
    simpa only [Option.bind_some,hs] using hr3
  rw [show 2*k+3=(k+1)+(k+2) by omega,BB429Escape.run_add,hr1]
  simpa only [Option.bind_some] using h23

theorem exceptional_low_to_U (k w r:Nat)
  (hk:6≤k) (hm:k%4=2) (hw:w%4=0) (hrm:r%4=2)
  (heq:w+r+4=2*rayU k) (hr:r=3*k+8):
  run (2*k+3) (rayU k,w)=some (rayU (k+1),3*k+5) := by
  have hr1:= short_U k w r (2*rayU k-2) hk hm hw hrm heq (by omega)
  have hu:2≤rayU k:=by have h:=U_linear k (by omega);omega
  have hr2:run 1 (rayU k,2*rayU k-2)=some (0,4*rayU k+8):=by
    change next (rayU k,2*rayU k-2)=_
    exact near_down_reset (rayU k) hu
  have hbal:=ray_balance (k+1)
  have h2:rayU (k+1)=2*rayU k+3:=by rfl
  have hd:rayDemand (k+1)≤4*rayU k+8:=by omega
  have hr3:=ray_run (k+1) (4*rayU k+8) hd
  have hs:(4*rayU k+8)-rayDemand (k+1)=3*k+5:=by omega
  have h23:run (k+2) (rayU k,2*rayU k-2)=some (rayU (k+1),3*k+5):=by
    rw [show k+2=1+(k+1) by omega,BB429Escape.run_add,hr2]
    simpa only [Option.bind_some,hs] using hr3
  rw [show 2*k+3=(k+1)+(k+2) by omega,BB429Escape.run_add,hr1]
  simpa only [Option.bind_some] using h23

theorem exceptional_high_second_U (k:Nat)
  (hk:6≤k) (hm:k%4=2):
  run (k+3) (rayU (k+1),3*k+15) =
    some (rayU (k+1),6*k+35) := by
  let u:=rayU (k+1)
  let z:=3*k+15
  have hum:u%2=1:=by have hh:=U_mod (k+1) (by omega);dsimp [u];omega
  have hub:3≤u:=by have hh:=U_linear (k+1) (by omega);dsimp [u];omega
  have hzm:z%4=1:=by dsimp [z];omega
  have hzb:3*z≤2*u+1:=by
    have hh:=U_strong (k-2) (by omega)
    have hp:k-2+3=k+1:=by omega
    rw [hp] at hh
    dsimp [u,z]
    omega
  have htwo:=BB429OddExtension.odd_odd_two_step u z hum hub hzm hzb
  have hbalance:=ray_balance (k+1)
  have hbd:rayDemand (k+1)≤2*u+z+17:=by omega
  have hrun:=ray_run (k+1) (2*u+z+17) hbd
  have hcalc:(2*u+z+17)-rayDemand (k+1)=6*k+35:=by
    have hnext:rayU (k+1)=u:=rfl
    omega
  rw [show k+3=2+(k+1) by omega,BB429Escape.run_add,htwo]
  simpa only [Option.bind_some,u,z,hcalc] using hrun

theorem exceptional_high_to_V_even (k w r:Nat)
  (hk:6≤k) (hm:k%4=2) (hw:w%4=0) (hrm:r%4=2)
  (heq:w+r+4=2*rayU k) (hr:r=3*k+4):
  ∃ y:Nat,run (4*k+6) (rayU k,w)=some (rayV (k-2),y) ∧
    y%4=2 ∧ y+4≤2*rayV (k-2) := by
  have ha:=exceptional_high_to_U k w r hk hm hw hrm heq hr
  have hb:=exceptional_high_second_U k hk hm
  have hc:run (3*k+6) (rayU k,w)=some (rayU (k+1),6*k+35):=by
    rw [show 3*k+6=(2*k+3)+(k+3) by omega, BB429Escape.run_add,ha]
    simpa only [Option.bind_some] using hb
  have hl:k-2+3=k+1:=by omega
  have hzm:(6*k+35)%4=3:=by omega
  have hzb:6*k+35≤6*(k-2)+47:=by omega
  obtain ⟨y,hy,hm2,hg⟩:=U_to_V_good (k-2) (rayU (k+1)) (6*k+35)
    (by rw [hl]) (by omega) (by omega) hzm hzb
  refine ⟨y, ?_, hm2, hg⟩
  rw [show 4*k+6=(3*k+6)+k by omega,BB429Escape.run_add,hc]
  have htime:(k-2)+2=k:=by omega
  simpa only [Option.bind_some,htime] using hy

theorem exceptional_low_to_V_even (k w r:Nat)
  (hk:6≤k) (hm:k%4=2) (hw:w%4=0) (hrm:r%4=2)
  (heq:w+r+4=2*rayU k) (hr:r=3*k+8):
  ∃ y:Nat,run (3*k+3) (rayU k,w)=some (rayV (k-2),y) ∧
    y%4=2 ∧ y+4≤2*rayV (k-2) := by
  have ha:=exceptional_low_to_U k w r hk hm hw hrm heq hr
  have hl:k-2+3=k+1:=by omega
  have hzm:(3*k+5)%4=3:=by omega
  have hzb:3*k+5≤6*(k-2)+47:=by omega
  obtain ⟨y,hy,hm2,hg⟩:=U_to_V_good (k-2) (rayU (k+1)) (3*k+5)
    (by rw [hl]) (by omega) (by omega) hzm hzb
  refine ⟨y, ?_, hm2, hg⟩
  rw [show 3*k+3=(2*k+3)+k by omega,BB429Escape.run_add,ha]
  have htime:(k-2)+2=k:=by omega
  simpa only [Option.bind_some,htime] using hy

/-- Exhaustive transfer of every U-even corridor endpoint at k>=6, k%4=2. -/
theorem U_even_complete_transfer (k w r:Nat)
  (hk:6≤k) (hm:k%4=2) (hw:w%4=0) (hrm:r%4=2)
  (heq:w+r+4=2*rayU k) (hbound:r<3*k+10):
  ∃ n y:Nat,
    (n=2*k+2 ∨ n=3*k+3 ∨ n=4*k+6) ∧
    run n (rayU k,w)=some (rayV (k-2),y) ∧
    y%4=2 ∧ y+4≤2*rayV (k-2) := by
  have hcases:r≤3*k+2 ∨ r=3*k+4 ∨ r=3*k+8:=by omega
  rcases hcases with htyp | hhigh | hlow
  · let z:Nat:=3*k+3-r
    have hz:z+r=3*k+3:=by dsimp [z];omega
    obtain ⟨y,hy,hy2,hg⟩:=typical_U_to_V_even k w r z
      hk hm hw hrm heq htyp hz
    exact ⟨2*k+2,y,Or.inl rfl,hy,hy2,hg⟩
  · obtain ⟨y,hy,hy2,hg⟩:=exceptional_high_to_V_even k w r
      hk hm hw hrm heq hhigh
    exact ⟨4*k+6,y,Or.inr (Or.inr rfl),hy,hy2,hg⟩
  · obtain ⟨y,hy,hy2,hg⟩:=exceptional_low_to_V_even k w r
      hk hm hw hrm heq hlow
    exact ⟨3*k+3,y,Or.inr (Or.inl rfl),hy,hy2,hg⟩

#print axioms U_even_complete_transfer
#print axioms exceptional_high_to_V_even
#print axioms exceptional_low_to_V_even
#print axioms exceptional_high_to_U
#print axioms exceptional_low_to_U
end BB429CorridorExceptions
