import CorridorExceptions
import Lean.Elab.Tactic.Omega

/-!
All-parameter bridge from any admissible U-even ladder state to the V-even
ladder, for the source-transcribed accelerated map of BB(6) machine #429.
This does not assert perpetual nonhalting or a genuine-blank halting decision.
-/
namespace BB429WholeCorridor
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer BB429CorridorExceptions

/-- Exact quotient/remainder discharge of all U-even loop counts and exits. -/
theorem whole_U_even_to_V_even (k w:Nat)
  (hk:6≤k) (hmod:k%4=2) (hw:w%4=0) (hguard:w+4≤2*rayU k) :
  ∃ N y:Nat,
    run N (rayU k,w)=some (rayV (k-2),y) ∧
    y%4=2 ∧ y+4≤2*rayV (k-2) := by
  let delta:Nat:=3*k+10
  let cap:Nat:=2*rayU k-w-4
  let m:Nat:=cap/delta
  let r:Nat:=cap%delta
  let wfinal:Nat:=w+m*delta
  have hc:cap+w+4=2*rayU k:=by dsimp [cap];omega
  have hdelta:0<delta:=by dsimp [delta];omega
  have hdelta4:delta%4=0:=by dsimp [delta];omega
  have hmod_eucl:r+delta*m=cap:=Nat.mod_add_div cap delta
  have hmod_small:r<delta:=Nat.mod_lt cap hdelta
  have hcomm:m*delta=delta*m:=Nat.mul_comm m delta
  have hprod:(delta*m)%4=0:=by simp [Nat.mul_mod,hdelta4]
  have hcap4:cap%4=2:=by
    have hu:=U_mod k (by omega)
    omega
  have hr4:r%4=2:=by omega
  have hwfinalmod:wfinal%4=0:=by
    dsimp [wfinal]
    have hprod2:(m*delta)%4=0:=by rw [hcomm]; exact hprod
    omega
  have heqfinal:wfinal+r+4=2*rayU k:=by
    dsimp [wfinal]
    omega
  have hguardfinal:wfinal+4≤2*rayU k:=by omega
  have hrun:=BB429Ladder.ray_ladder k m w (by omega) hmod hw hguardfinal
  have htransfer:=U_even_complete_transfer k wfinal r hk hmod hwfinalmod hr4
    heqfinal (by dsimp [delta] at hmod_small; omega)
  obtain ⟨n,y,_,ht,hy,hguardY⟩:=htransfer
  refine ⟨m*(k+1)+n,y,?_,hy,hguardY⟩
  rw [BB429.run_add,hrun]
  simpa only [Option.bind_some,wfinal] using ht

#print axioms whole_U_even_to_V_even
end BB429WholeCorridor
