import CrossRayReturn
import OddBoundary
import Lean.Elab.Tactic.Omega

/-!
A complete return-or-overflow classification of the odd V_(l+1) phase
for BB429's source-transcribed exact accelerated map.

The two-phase split is uniform in l and w. It assumes an actual admissible
V-odd state, and asserts no all-time blank nonhalting or BB(6) bound.
-/
namespace BB429CrossRayOverflow
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

/-- A uniform linear margin between the U and V exponential rays. -/
theorem cross_budget (l:Nat) (hl:4≤l):
    8*rayV (l+1)+9*(l+3)+73≤12*rayU (l+3):=by
  obtain ⟨n,hn⟩ : ∃ n, l=n+4 := ⟨l-4,by omega⟩
  subst l
  induction n with
  | zero => decide
  | succ n ih =>
    have h1:n+1+4+1=(n+4+1)+1 := by omega
    have h2:n+1+4+3=(n+4+3)+1 := by omega
    rw [h1,h2]
    change 8*(2*rayV (n+4+1)+3)+9*((n+4+3)+1)+73 ≤
      12*(2*rayU (n+4+3)+3)
    omega

/-- Every odd-V overflow is a certified finite word via U_(l+3);
the natural-number subtraction is valid under the proved margin. -/
theorem cross_ray_overflow (l w:Nat) (hl:4≤l) (hm:l%4=0) (hw:w%4=1)
    (hfirst:3*w≤2*rayV (l+1)+1)
    (hfail:8*rayU (l+3)<3*w+6*rayV (l+1)+9*(l+3)+36):
    let z:=2*rayV (l+1)+w+17-rayDemand (l+3)
    run (l+7) (rayV (l+1),w)=
      some (2*rayU (l+3)-z+18,3*z-2*rayU (l+3)-22) := by
  let i:=l+1
  let j:=l+3
  let v:=rayV i
  let u:=rayU j
  let W0:=2*v+w+17
  let z:=W0-rayDemand j
  have horder:u≤v:=by dsimp [u,v,i,j]; exact BB429CrossRayReturn.cross_ray_order l
  have hodd:v%2=1:=by dsimp [v];exact vU_odd i
  have hlarge:3≤v:=by have h:=vU_large i;dsimp [v] at *;omega
  have htwo:run 2 (v,w)=some (0,W0):=by
    dsimp [W0]
    exact BB429OddExtension.odd_odd_two_step v w hodd hlarge hw
      (by dsimp [v,i] at *;exact hfirst)
  have hb:=ray_balance j
  have hdb:rayDemand j≤W0:=by dsimp [W0];omega
  have hray:=ray_run j W0 hdb
  have hZ:z+rayDemand j=W0:=by dsimp [z];omega
  have hu4:u%4=1:=by dsimp [u,j];exact U_mod (l+3) (by omega)
  have hv4:v%4=1:=by dsimp [v,i];exact V_mod (l+1) (by omega)
  have hj4:j%4=3:=by dsimp [j];omega
  have hz4:z%4=3:=by dsimp [W0] at hZ;omega
  have hbudget:=cross_budget l hl
  have hcap:z+7≤2*u:=by
    dsimp [u,v,j,i,W0] at *
    omega
  have hfailReturn: ¬ 3*z≤2*u+15 := by
    intro hret
    dsimp [u,v,j,i,W0] at *
    omega
  have hcases:=BB429OddBoundary.rayU_odd_boundary j z (by dsimp[j];omega)
    hz4 hcap
  have hstep:run 2 (u,z)=some (2*u-z+18,3*z-2*u-22):=by
    rcases hcases with ⟨hret,_⟩ | ⟨_,hx⟩
    · exact False.elim (hfailReturn hret)
    · simpa only [u] using hx
  have hfirstRun:run (2+j) (v,w)=some (u,z):=by
    rw [BB429.run_add,htwo]
    simpa only [Option.bind_some,u,z] using hray
  have htotal:l+7=(2+j)+2:=by dsimp [j];omega
  change run (l+7) (v,w)=some (2*u-z+18,3*z-2*u-22)
  rw [htotal,BB429.run_add,hfirstRun]
  simpa only [Option.bind_some] using hstep

/-- Conditional complete odd-V transition classification. -/
theorem cross_ray_complete_split (l w:Nat) (hl:4≤l) (hm:l%4=0) (hw:w%4=1)
    (hfirst:3*w≤2*rayV (l+1)+1):
    (3*w+6*rayV (l+1)+9*(l+3)+36≤8*rayU (l+3) ∧
      run (2*l+8) (rayV (l+1),w)=some (rayV (l+1),w+6*l+60)) ∨
    (8*rayU (l+3)<3*w+6*rayV (l+1)+9*(l+3)+36 ∧
      let z:=2*rayV (l+1)+w+17-rayDemand (l+3)
      run (l+7) (rayV (l+1),w)=
        some (2*rayU (l+3)-z+18,3*z-2*rayU (l+3)-22)) := by
  by_cases h:3*w+6*rayV (l+1)+9*(l+3)+36≤8*rayU (l+3)
  · exact Or.inl ⟨h,BB429CrossRayReturn.cross_ray_return l w hl hm hw h⟩
  · have hf:8*rayU (l+3)<3*w+6*rayV (l+1)+9*(l+3)+36:=by omega
    exact Or.inr ⟨hf,cross_ray_overflow l w hl hm hw hfirst hf⟩

/-- The first actual blank-derived odd-V overflow is reached at macro 213. -/
theorem rooted_to_513_17 : run 213 (0,0)=some (513,17) := by
  have h202:=BB429CrossRayReturn.rooted_to_V5_101
  have hV5:rayV 5=445:=by decide
  have h11:run 11 (rayV 5,101)=some (513,17):=by
    rw [hV5]
    decide
  rw [show 213=202+11 by decide,BB429.run_add,h202]
  simpa only [Option.bind_some] using h11

#print axioms cross_budget
#print axioms cross_ray_overflow
#print axioms cross_ray_complete_split
#print axioms rooted_to_513_17
end BB429CrossRayOverflow
