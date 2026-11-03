import VExitTransfer
import Lean.Elab.Tactic.Omega

/-!
The complementary whole-V-even corridor theorem and an explicitly
composed, genuine blank-origin #429 prefix through the proven U/V sectors.
This is finite source-connected progress, not a global root nonhalting proof.
-/
namespace BB429VWholeCorridor
open BB429 BB429Ladder BB429ElevenExtension BB429VExitTransfer

theorem whole_V_even_to_V_odd (l w:Nat)
  (hl:4≤l) (hm:l%4=0) (hw:w%4=2) (hguard:w+4≤2*rayV l):
  ∃ n z:Nat,
    run n (rayV l,w)=some (rayV (l+1),z) ∧ z%4=1 := by
  let delta:=3*l+20
  let cap:=2*rayV l-w-4
  let m:=cap/delta
  let r:=cap%delta
  let wlast:=w+m*delta
  have hcap:cap+w+4=2*rayV l:=by dsimp [cap];omega
  have hdelta:0<delta:=by dsimp [delta];omega
  have hdelta4:delta%4=0:=by dsimp [delta];omega
  have he:r+delta*m=cap:=Nat.mod_add_div cap delta
  have hrlt:r<delta:=Nat.mod_lt cap hdelta
  have hcomm:m*delta=delta*m:=Nat.mul_comm m delta
  have hprod:(delta*m)%4=0:=by simp [Nat.mul_mod,hdelta4]
  have hcap4:cap%4=0:=by have hv:=V_mod l (by omega);omega
  have hr4:r%4=0:=by omega
  have hwlast4:wlast%4=2:=by
    have hp:(m*delta)%4=0:=by rw [hcomm];exact hprod
    dsimp [wlast]
    omega
  have hlast:wlast+r+4=2*rayV l:=by dsimp [wlast];omega
  have hlastguard:wlast+4≤2*rayV l:=by omega
  have hrun:=v_even_ladder l m w hm hw hlastguard
  have htrans:=V_even_complete_transfer l wlast r hl hm hwlast4 hr4
    hlast (by dsimp [delta] at hrlt;omega)
  obtain ⟨t,z,_,ht,hz⟩:=htrans
  refine ⟨m*(l+1)+t,z,?_,hz⟩
  rw [BB429.run_add,hrun]
  simpa only [Option.bind_some,wlast] using ht

/-- A real blank-origin chain, composed from the parametrized sector lemmas. -/
theorem rooted_to_V5_17 : run 186 (0,0)=some (rayV 5,17) := by
  have h0:=BB429Ladder.root_to_189_48
  have h1:=BB429Ladder.ray_ladder 6 11 48 (by decide) (by decide) (by decide) (by decide)
  have h1a:rayU 6=189:=by decide
  have h1b:48+11*(3*6+10)=356:=by decide
  have h2:=BB429ExitTransfer.typical_U_to_V 6 356 18 3
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2a:rayV 4=221:=by decide
  have h2b:(2*rayU (6+1)+3+9)-demandV (6-2)=366:=by decide
  have h3:=BB429ElevenExtension.v_even_ladder 4 2 366
    (by decide) (by decide) (by decide)
  have h3b:366+2*(3*4+20)=430:=by decide
  have h4:=BB429VExitTransfer.V_regular_to_next 4 430 8 17
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hstep1:run 77 (189,48)=some (189,356):=by simpa [h1a,h1b] using h1
  have hstep2:run 14 (189,356)=some (221,366):=by simpa [h1a,h2a,h2b] using h2
  have hstep3:run 10 (221,366)=some (221,430):=by simpa [h2a,h3b] using h3
  have hstep4:run 6 (221,430)=some (rayV 5,17):=by simpa [h2a] using h4
  calc
    run 186 (0,0) = (run 79 (0,0)).bind (run 107) := by
      simpa only [show 186=79+107 by decide] using BB429.run_add 79 107 (0,0)
    _ = (run 77 (189,48)).bind (run 30) := by
      rw [h0]
      simp only [Option.bind_some]
      simpa only [show 107=77+30 by decide] using BB429.run_add 77 30 (189,48)
    _ = (run 14 (189,356)).bind (run 16) := by
      rw [hstep1]
      simp only [Option.bind_some]
      simpa only [show 30=14+16 by decide] using BB429.run_add 14 16 (189,356)
    _ = (run 10 (221,366)).bind (run 6) := by
      rw [hstep2]
      simp only [Option.bind_some]
      simpa only [show 16=10+6 by decide] using BB429.run_add 10 6 (221,366)
    _ = some (rayV 5,17) := by simp [hstep3,hstep4]

#print axioms whole_V_even_to_V_odd
#print axioms rooted_to_V5_17
end BB429VWholeCorridor
