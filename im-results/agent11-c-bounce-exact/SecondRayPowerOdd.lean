import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray

private theorem pow_four_pos (n:Nat) : 0<4^n := Nat.pow_pos (by decide)

private theorem power_split (s t:Nat) : 4^(s+t)=4^s*4^t := Nat.pow_add 4 s t

/-- The target has an odd unit factor when m is odd, while a+3 is even.
    Therefore its high-bounce depth cannot reach the total 4-adic exponent. -/
theorem odd_ray_exponent_bound (m s a : Nat)
    (hm : m%2=1) (ha : a%2=1)
    (h : 4^(m+1)*(3*m+4)=4^(s+1)*(a+3)) :
    s<m := by
  by_cases hlt : s<m
  · exact hlt
  have hms:m≤s := by omega
  exfalso
  have hs : s+1=(m+1)+(s-m) := by omega
  have hsplit : 4^(s+1)=4^(m+1)*4^(s-m) := by
    rw [hs,Nat.pow_add]
  rw [hsplit] at h
  have hc : 3*m+4=4^(s-m)*(a+3) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_four_pos (m+1))
    calc
      4^(m+1)*(3*m+4) = (4^(m+1)*4^(s-m))*(a+3) := h
      _ = 4^(m+1)*(4^(s-m)*(a+3)) := by ac_rfl
  have haeven : 2 ∣ (a+3) := by
    refine ⟨(a+3)/2,?_⟩
    omega
  obtain ⟨z,hz⟩ := haeven
  have heven : 2 ∣ 4^(s-m)*(a+3) := by
    refine ⟨4^(s-m)*z,?_⟩
    rw [hz]
    ac_rfl
  have hmod : (4^(s-m)*(a+3))%2=0 := Nat.mod_eq_zero_of_dvd heven
  omega

theorem odd_ray_factor (m s a:Nat)
    (hm:m%2=1) (ha:a%2=1)
    (h:4^(m+1)*(3*m+4)=4^(s+1)*(a+3)) :
    s<m ∧ a+3=4^(m-s)*(3*m+4) := by
  have hlt := odd_ray_exponent_bound m s a hm ha h
  constructor
  · exact hlt
  · have hmex : m+1=(s+1)+(m-s) := by omega
    have hsplit : 4^(m+1)=4^(s+1)*4^(m-s) := by
      rw [hmex,Nat.pow_add]
    rw [hsplit] at h
    have hc : 4^(m-s)*(3*m+4)=a+3 := by
      apply Nat.eq_of_mul_eq_mul_left (pow_four_pos (s+1))
      calc
        4^(s+1)*(4^(m-s)*(3*m+4)) = (4^(s+1)*4^(m-s))*(3*m+4) := by ac_rfl
        _ = 4^(s+1)*(a+3) := h
    exact hc.symm

theorem odd_number_not_power_two (b n : Nat)
    (hb : b%2=1) (hbig : 1<b) : b≠2^n := by
  intro h
  cases n with
  | zero => simp at h; omega
  | succ n =>
      rw [Nat.pow_succ] at h
      omega

/-- For odd m the odd factor 3m+4 >1 prevents the target D
    from being any pure power of two. -/
theorem odd_ray_D_not_pow_two (m e : Nat) (hm:m%2=1) :
    4^(m+1)*(3*m+4) ≠ 2^e := by
  intro h
  have hf : 4^(m+1)=2^(2*(m+1)) := by
    calc
      4^(m+1) = (2^2)^(m+1) := by simp
      _ = 2^(2*(m+1)) := (Nat.pow_mul 2 2 (m+1)).symm
  rw [hf] at h
  have hB : (3*m+4)%2=1 := by omega
  have hBig : 1<3*m+4 := by omega
  by_cases hle : e≤2*(m+1)
  · have hlepow : 2^e≤2^(2*(m+1)) :=
      Nat.pow_le_pow_right (by decide) hle
    have hbigmul : 2^(2*(m+1)) < 2^(2*(m+1))*(3*m+4) := by
      have hp : 0<2^(2*(m+1)) := Nat.pow_pos (by decide)
      have hh := Nat.mul_lt_mul_of_pos_left hBig hp
      simpa using hh
    omega
  · have he : 2*(m+1)≤e := by omega
    have hsplit : 2^e=2^(2*(m+1))*2^(e-2*(m+1)) := by
      have heq : e=2*(m+1)+(e-2*(m+1)) := by omega
      calc
        2^e = 2^(2*(m+1)+(e-2*(m+1))) := by congr 1
        _ = 2^(2*(m+1))*2^(e-2*(m+1)) := Nat.pow_add 2 _ _
    rw [hsplit] at h
    have hc : 3*m+4=2^(e-2*(m+1)) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) h
    exact odd_number_not_power_two (3*m+4) (e-2*(m+1)) hB hBig hc

#print axioms odd_ray_factor
end BB6.Agent11Ray

namespace BB6.Agent11Ray

theorem odd_high_parent_normalized (m a k : Nat)
    (hm : m%2=1) (ha : a%2=1)
    (h : ∃ n:Nat, n%2=1 ∧
      4^(m+1)*(3*m+4)=2^(n+1)*(a+3) ∧
      2*k+a+7+3*n=(6*m+5)+2*(4^(m+1)*(3*m+4)-(6*m+6))) :
    ∃ s t : Nat, m=s+t+1 ∧
      a+3=4^(t+1)*(3*m+4) ∧
      k+(2*4^t*(3*m+4)+3*m+7+3*s)=4^(m+1)*(3*m+4) := by
  obtain ⟨n,hn,hp,hc⟩:=h
  let s:=n/2
  have hns : n=2*s+1 := by dsimp [s];omega
  have h2p : 2^(n+1)=4^(s+1) := by
    rw [hns]
    have hcalc : 2*s+1+1=2*(s+1) := by omega
    rw [hcalc,Nat.pow_mul]
  rw [h2p] at hp
  have hh := odd_ray_factor m s a hm ha hp
  let t:=m-s-1
  have hstm : m=s+t+1 := by dsimp [t];omega
  have hta : t+1=m-s := by dsimp [t];omega
  have hA : a+3=4^(t+1)*(3*m+4) := by
    rw [hta]
    exact hh.2
  have hA2 : a+3=4*(4^t*(3*m+4)) := by
    rw [hA,Nat.pow_succ]
    ac_rfl
  have hd : 6*m+6≤4^(m+1)*(3*m+4) := by
    have hs : 4≤4^(m+1) := by
      rw [show m+1=1+m by omega,Nat.pow_add]
      have hp : 1≤4^m:=Nat.one_le_pow m 4 (by decide)
      omega
    have hmul : 4*(3*m+4) ≤ 4^(m+1)*(3*m+4) :=
      Nat.mul_le_mul_right (3*m+4) hs
    omega
  have hcost : k+(2*4^t*(3*m+4)+3*m+7+3*s)=4^(m+1)*(3*m+4) := by
    have hpp : 2*4^t*(3*m+4)=2*(4^t*(3*m+4)) := by ac_rfl
    rw [hpp]
    omega
  exact ⟨s,t,hstm,hA,hcost⟩

#print axioms odd_high_parent_normalized
#print axioms odd_ray_D_not_pow_two
end BB6.Agent11Ray
