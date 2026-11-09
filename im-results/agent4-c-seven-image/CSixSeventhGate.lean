import CSixSeventhRoot
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 250000

namespace BB6.Agent4Seven
open BB6.Agent46

private theorem margin_seven (q : Nat) :
    3*(q+7)+600 ≤ (2:Nat)^(2*(q+7)+2) := by
  induction q with
  | zero => decide
  | succ q ih =>
      have he : 2*((q+1)+7)+2=(2*(q+7)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem stopping_target_lower (j m k P : Nat)
    (hb : 3*m+600 ≤ P) (hp : 1≤P)
    (hstop : k+j+3*m+5=P*(j+3)) : 574≤k := by
  have hjmul : j≤P*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add] at hstop
  have hmul : P*j+P*3=P*j+3*P := by omega
  rw [hmul] at hstop
  omega

private theorem j_coordinate (j : Nat) (hj : j%2048=319) :
    2*j+3=641+4096*((j-319)/2048) := by omega

private theorem k_coordinate (k : Nat) (hk : k%16384=574) :
    k=574+16384*((k-574)/16384) := by omega

/-- Original high stopping equation implies an authentic blank-origin exclusion
    on a previously unexhibited strict sixth-versus-seventh image band. -/
theorem high_stop_six_seven_blank_exclusion (j m k time : Nat)
    (hm : 7≤m) (hj : j%2048=319)
    (hpair : (j+3*m)%16384=15805)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  let P := (2:Nat)^(2*m+2)
  have hstop' : k+j+3*m+5=P*(j+3) := by simpa only [P] using hstop
  have hp : 16384∣P := by
    have hdiv : (2:Nat)^14 ∣ (2:Nat)^(2*m+2) := Nat.pow_dvd_pow 2 (by omega)
    simpa only [P, show (2:Nat)^14=16384 by decide] using hdiv
  obtain ⟨z,hz⟩ := hp
  have hmod : (k+j+3*m+5)%16384=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨z*(j+3),?_⟩
    calc
      k+j+3*m+5=P*(j+3) := hstop'
      _=(16384*z)*(j+3) := by rw [hz]
      _=16384*(z*(j+3)) := by ac_rfl
  have hkmod : k%16384=574 := by omega
  have hpbound : 3*m+600≤P := by
    have h := margin_seven (m-7)
    simpa only [Nat.sub_add_cancel hm] using h
  have hpone : 1≤P := by omega
  have hlarge : 574≤k := stopping_target_lower j m k P hpbound hpone hstop'
  let u : Nat := (j-319)/2048
  let v : Nat := (k-574)/16384
  have hx : 2*j+3=641+4096*u := j_coordinate j hj
  have hy : k=574+16384*v := k_coordinate k hkmod
  rw [hx,hy]
  exact blank_ne_six_seven_band u v time

#print axioms high_stop_six_seven_blank_exclusion
end BB6.Agent4Seven
