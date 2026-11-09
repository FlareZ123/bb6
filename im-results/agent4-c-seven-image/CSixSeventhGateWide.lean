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

private theorem params_case0 (j m k : Nat) (hj : j%2048=319)
    (hm : (j+3*m)%4096=3517) (hk:(k+j+3*m+5)%4096=0)
    (hlarge : 574≤k) :
    ∃u v:Nat, 2*j+3=641+1024*u ∧ k=574+1024*v ∧ (u+v)%4=0 := by
  have hkr : k%4096=574 := by omega
  refine ⟨(j-319)/512,(k-574)/1024, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

private theorem params_case1 (j m k : Nat) (hj : j%2048=831)
    (hm : (j+3*m)%4096=445) (hk:(k+j+3*m+5)%4096=0)
    (hlarge : 574≤k) :
    ∃u v:Nat, 2*j+3=641+1024*u ∧ k=574+1024*v ∧ (u+v)%4=0 := by
  have hkr : k%4096=3646 := by omega
  refine ⟨(j-319)/512,(k-574)/1024, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

private theorem params_case2 (j m k : Nat) (hj : j%2048=1343)
    (hm : (j+3*m)%4096=1469) (hk:(k+j+3*m+5)%4096=0)
    (hlarge : 574≤k) :
    ∃u v:Nat, 2*j+3=641+1024*u ∧ k=574+1024*v ∧ (u+v)%4=0 := by
  have hkr : k%4096=2622 := by omega
  refine ⟨(j-319)/512,(k-574)/1024, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

private theorem params_case3 (j m k : Nat) (hj : j%2048=1855)
    (hm : (j+3*m)%4096=2493) (hk:(k+j+3*m+5)%4096=0)
    (hlarge : 574≤k) :
    ∃u v:Nat, 2*j+3=641+1024*u ∧ k=574+1024*v ∧ (u+v)%4=0 := by
  have hkr : k%4096=1598 := by omega
  refine ⟨(j-319)/512,(k-574)/1024, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Four disjoint original high-stop classes pull back into the widened sharp image band. -/
theorem high_stop_six_seven_fourclass_exclusion (j m k time : Nat)
    (hm : 7≤m)
    (hparams : (j%2048=319 ∧ (j+3*m)%4096=3517) ∨
      (j%2048=831 ∧ (j+3*m)%4096=445) ∨
      (j%2048=1343 ∧ (j+3*m)%4096=1469) ∨
      (j%2048=1855 ∧ (j+3*m)%4096=2493))
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  let P := (2:Nat)^(2*m+2)
  have hstop' : k+j+3*m+5=P*(j+3) := by simpa only [P] using hstop
  have hp : 4096∣P := by
    have hdiv : (2:Nat)^12 ∣ (2:Nat)^(2*m+2) := Nat.pow_dvd_pow 2 (by omega)
    simpa only [P, show (2:Nat)^12=4096 by decide] using hdiv
  obtain ⟨z,hz⟩ := hp
  have hmod : (k+j+3*m+5)%4096=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨z*(j+3),?_⟩
    calc
      k+j+3*m+5=P*(j+3) := hstop'
      _=(4096*z)*(j+3) := by rw [hz]
      _=4096*(z*(j+3)) := by ac_rfl
  have hpbound : 3*m+600≤P := by
    have h := margin_seven (m-7)
    simpa only [Nat.sub_add_cancel hm] using h
  have hpone : 1≤P := by omega
  have hlarge : 574≤k := stopping_target_lower j m k P hpbound hpone hstop'
  rcases hparams with h0|h1|h2|h3
  · obtain ⟨u,v,hx,hy,huv⟩ := params_case0 j m k h0.1 h0.2 hmod hlarge
    rw [hx,hy]
    exact blank_ne_six_seven_band u v time huv
  · obtain ⟨u,v,hx,hy,huv⟩ := params_case1 j m k h1.1 h1.2 hmod hlarge
    rw [hx,hy]
    exact blank_ne_six_seven_band u v time huv
  · obtain ⟨u,v,hx,hy,huv⟩ := params_case2 j m k h2.1 h2.2 hmod hlarge
    rw [hx,hy]
    exact blank_ne_six_seven_band u v time huv
  · obtain ⟨u,v,hx,hy,huv⟩ := params_case3 j m k h3.1 h3.2 hmod hlarge
    rw [hx,hy]
    exact blank_ne_six_seven_band u v time huv

#print axioms high_stop_six_seven_fourclass_exclusion
end BB6.Agent4Seven
