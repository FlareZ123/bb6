import CapTerminalBand

namespace CapModNoGo
open CapSieve

def F (k : Nat) : Nat := 2*P k+k

theorem exp_period_witness (s : Nat) :
    ∃ c : Nat, 2^(2*3^s)=1+3^(s+1)*c := by
  induction s with
  | zero => exact ⟨1,by decide⟩
  | succ s ih =>
    obtain ⟨c,hc⟩ := ih
    refine ⟨c+3*3^s*c*c+3*3^s*3^s*c*c*c,?_⟩
    rw [show 2*3^(s+1)=(2*3^s)*3 by rw [Nat.pow_succ,Nat.mul_assoc],Nat.pow_mul,hc]
    simp only [Nat.pow_succ (n:=3)]
    grind

theorem exp_period (s : Nat) : 2^(2*3^s) % 3^(s+1)=1 := by
  obtain ⟨c,hc⟩ := exp_period_witness s
  rw [hc,Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  rw [Nat.pow_succ]
  have h : 0<3^s := Nat.pow_pos (by decide)
  omega

theorem exp_period_multiple (s t : Nat) :
    2^(2*3^s*t)%3^(s+1)=1 := by
  rw [Nat.pow_mul,Nat.pow_mod,exp_period,Nat.one_pow]
  exact Nat.mod_eq_of_lt (by
    rw [Nat.pow_succ]
    have h : 0<3^s := Nat.pow_pos (by decide)
    omega)

theorem F_shift (k s t : Nat) :
    F (k+2*3^s*t)%3^(s+1)=(F k+2*3^s*t)%3^(s+1) := by
  have he : (2*P (k+2*3^s*t))%3^(s+1)=(2*P k)%3^(s+1) := by
    unfold P
    rw [Nat.pow_add,show 2*(5*(2^k*2^(2*3^s*t)))=(2*(5*2^k))*2^(2*3^s*t) by ac_rfl]
    rw [Nat.mul_mod,exp_period_multiple,Nat.mul_one,Nat.mod_mod]
  unfold F
  rw [show 2*P k+k+2*3^s*t=2*P k+(k+2*3^s*t) by omega]
  rw [Nat.add_mod (2*P (k+2*3^s*t)) _,Nat.add_mod (2*P k) _,he]

theorem lift_digit (D A B : Nat) (hD : 0<D) (h : A%D=B%D) :
    ∃ t : Nat, t<3 ∧ (A+2*D*t)%(3*D)=B%(3*D) := by
  let a := A/D
  let b := B/D
  let z := A%D
  have ha : A=z+D*a := by dsimp [z,a]; exact (Nat.mod_add_div A D).symm
  have hb : B=z+D*b := by dsimp [z,b]; rw [h]; exact (Nat.mod_add_div B D).symm
  have hchoice : ∃ t : Nat, t<3 ∧ (a+2*t)%3=b%3 := by
    have hcases : a%3=b%3 ∨ (a+2)%3=b%3 ∨ (a+4)%3=b%3 := by omega
    rcases hcases with h|h|h
    · exact ⟨0,by decide,by simpa using h⟩
    · exact ⟨1,by decide,by simpa using h⟩
    · exact ⟨2,by decide,by simpa using h⟩
  obtain ⟨t,ht,he⟩ := hchoice
  refine ⟨t,ht,?_⟩
  rw [ha,hb,show z+D*a+2*D*t=z+D*(a+2*t) by grind]
  rw [show 3*D=D*3 by omega]
  rw [Nat.add_mod z _,Nat.add_mod z _,Nat.mul_mod_mul_left,Nat.mul_mod_mul_left,he]

/-- Arbitrary precision lifting of F along the prescribed parity progression. -/
theorem F_lift (h d k y : Nat) (he : F k%3^h=y%3^h) :
    ∃ t, F (k+2*3^h*t)%3^(h+d)=y%3^(h+d) := by
  induction d with
  | zero => exact ⟨0,by simpa using he⟩
  | succ d ih =>
    obtain ⟨t,ht⟩ := ih
    let x := k+2*3^h*t
    have hx : F x%3^(h+d)=y%3^(h+d) := ht
    obtain ⟨u,_,hu⟩ := lift_digit (3^(h+d)) (F x) y (Nat.pow_pos (by decide)) hx
    refine ⟨t+3^d*u,?_⟩
    have hs := F_shift x (h+d) u
    have he' : k+2*3^h*(t+3^d*u)=x+2*3^(h+d)*u := by
      dsimp [x]
      rw [Nat.pow_add]
      grind
    rw [he',show h+(d+1)=h+d+1 by omega,hs,Nat.pow_succ]
    rw [show 3^(h+d)*3=3*3^(h+d) by ac_rfl]
    exact hu

theorem F_shift_same (k s t : Nat) :
    F (k+2*3^s*t)%3^s=F k%3^s := by
  have hs := F_shift k s t
  have hd : 3^s ∣ 3^(s+1) := Nat.pow_dvd_pow 3 (by omega)
  have he := congrArg (fun x : Nat => x%3^s) hs
  rw [Nat.mod_mod_of_dvd _ hd,Nat.mod_mod_of_dvd _ hd] at he
  rw [he,show 2*3^s*t=3^s*(2*t) by ac_rfl,Nat.add_mul_mod_self_left]

/-- A root residue of F exists at every precision, in either parity. -/
theorem F_zero_residue (h parity : Nat) (hp : parity<2) :
    ∃ k, k%2=parity ∧ F k%3^h=0 := by
  obtain ⟨t,ht⟩ := F_lift 0 h parity 0 (by simp [Nat.mod_one])
  refine ⟨parity+2*t,by omega,?_⟩
  simpa using ht

/-- Lift a prescribed target while making the band index arbitrarily large. -/
theorem F_lift_unbounded (h d k y K : Nat) (he : F k%3^h=y%3^h) :
    ∃ j, K≤j ∧ j%(2*3^h)=k%(2*3^h) ∧ F j%3^(h+d)=y%3^(h+d) := by
  obtain ⟨t,ht⟩ := F_lift h d k y he
  let j := k+2*3^h*t+2*3^(h+d)*K
  have hpow : 0<3^(h+d) := Nat.pow_pos (by decide)
  have hj : K≤j := by
    dsimp [j]
    have hm := Nat.le_mul_of_pos_left K (show 0<2*3^(h+d) by omega)
    omega
  refine ⟨j,hj,?_,?_⟩
  · dsimp [j]
    rw [Nat.pow_add,show k+2*3^h*t+2*(3^h*3^d)*K=k+(2*3^h)*(t+3^d*K) by grind,
      Nat.add_mul_mod_self_left]
  · dsimp [j]
    rw [F_shift_same,ht]

#print axioms F_lift_unbounded
#print axioms F_zero_residue
end CapModNoGo
