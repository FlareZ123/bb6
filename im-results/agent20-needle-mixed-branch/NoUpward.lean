import Mathlib

namespace BB6.Agent20NoUpward

/-- A linear lower bound for the binary exponential, used only for v >= 2. -/
private theorem two_mul_le_two_pow (v : Nat) (hv : 2 ≤ v) :
    2*v ≤ 2^v := by
  induction v, hv using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      have hs : (2:Nat)^(n+1) = 2*2^n := by
        rw [pow_succ]
        ring
      rw [hs]
      omega

private theorem two_pow_doubles {v w : Nat} (h : v < w) :
    2*2^v ≤ 2^w := by
  obtain ⟨k,hk⟩ : ∃ k : Nat, w=v+1+k :=
    ⟨w-(v+1), by omega⟩
  have hkpos : 0 < (2:Nat)^k := pow_pos (by decide) _
  calc
    2*2^v = (2^v*2)*1 := by ring
    _ ≤ (2^v*2)*2^k := Nat.mul_le_mul_left _ (by omega)
    _ = 2^w := by rw [hk,pow_add,pow_succ]; ring

/-- For w >= 6 the exponential dominates the quadratic. -/
private theorem double_square_le_two_pow (w : Nat) (hw : 6 ≤ w) :
    2*w*w ≤ 2^(w+1) := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hs : (2:Nat)^(n+1+1)=2*2^(n+1) := by
        rw [pow_succ]
        ring
      have hsq : 6*n ≤ n*n := Nat.mul_le_mul_right n hn
      have hstep : 2*(n+1)*(n+1) ≤ 4*n*n := by
        nlinarith
      rw [hs]
      nlinarith

/-- Every upward pair has nonvanishing cross-potential difference modulo
    its larger-valuation incoming-edge denominator. -/
theorem no_upward_division (v w : Nat)
    (hv : 2 ≤ v) (hvw : v < w) :
    ¬ ((2^(w+1)+3) ∣ 3*(2^w*(2*w-3)-2^v*(2*v-3))) := by
  let D : Nat := 2^(w+1)+3
  let dv : Nat := 2^v*(2*v-3)
  let dw : Nat := 2^w*(2*w-3)
  let Q : Nat := dw-dv
  have hcV : 0<2*v-3 := by omega
  have hcW : 2*v-3 ≤ 2*w-3 := by omega
  have hp : 2*2^v ≤ 2^w := two_pow_doubles hvw
  have hpowerpos : 0<(2:Nat)^v := pow_pos (by decide) _
  have hposDv : 0<dv := by dsimp [dv]; positivity
  have horder : dv < dw := by
    dsimp [dv,dw]
    calc
      2^v*(2*v-3) < 2^w*(2*v-3) := by
        apply Nat.mul_lt_mul_of_pos_right
        · omega
        · exact hcV
      _ ≤ 2^w*(2*w-3) := Nat.mul_le_mul_left _ hcW
  have hQpos : 0<Q := by dsimp [Q]; omega
  have hQeq : Q+dv=dw := by dsimp [Q]; omega
  have hcop3 : D.Coprime 3 := by
    change (2^(w+1)+3).Coprime 3
    exact (Nat.coprime_add_self_left).mpr
      ((by decide : (2:Nat).Coprime 3).pow_left (w+1))
  intro h3Q
  have hQdiv : D ∣ Q := (Nat.Coprime.dvd_mul_left hcop3).mp h3Q
  have hpdiv : 2^v ∣ 2^w := Nat.pow_dvd_pow 2 (by omega)
  have hdwdiv : 2^v ∣ dw := by
    rcases hpdiv with ⟨s,hs⟩
    refine ⟨s*(2*w-3), ?_⟩
    dsimp [dw]
    rw [hs]
    ring
  have hdvdiv : 2^v ∣ dv := by
    exact ⟨2*v-3, by simp [dv]⟩
  have hQpowdiv : 2^v ∣ Q := by
    apply (Nat.dvd_add_iff_right hdvdiv).mpr
    rwa [hQeq]
  have hDodd : Odd D := by
    refine ⟨2^w+1, ?_⟩
    dsimp [D]
    rw [pow_succ]
    omega
  have hcop2 : (2^v).Coprime D :=
    (Nat.coprime_two_left.mpr hDodd).pow_left v
  rcases hQdiv with ⟨t,ht⟩
  have htpos : 0<t := by
    by_contra hn
    have ht0 : t=0 := by omega
    rw [ht0] at ht
    simp at ht
    omega
  have htdiv : 2^v ∣ t := by
    have hd : 2^v ∣ D*t := by rw [←ht]; exact hQpowdiv
    exact hcop2.dvd_of_dvd_mul_left hd
  have htbound : 2^v ≤ t := Nat.le_of_dvd htpos htdiv
  have hDge : 2^(w+1) ≤ D := by dsimp [D]; omega
  have hmulbound : (2^v)*D ≤ Q := by
    rw [ht]
    exact Nat.mul_le_mul_left D htbound |>.trans_eq (by ring)
  have hQlt : Q < 2^w*(2*w-3) := by
    dsimp [Q,dw]; omega
  have hcoeff : 2*2^v < 2*w-3 := by
    by_contra hn
    have hc : 2*w-3 ≤ 2*2^v := by omega
    have hpw : 2^(w+1)=2*2^w := by rw [pow_succ]; ring
    have hproduct : 2^w*(2*w-3) ≤ 2^w*(2*2^v) :=
      Nat.mul_le_mul_left _ hc
    have h2 : 2^v*2^(w+1) ≤ (2^v)*D :=
      Nat.mul_le_mul_left _ hDge
    rw [hpw] at h2
    nlinarith [hproduct,h2,hmulbound,hQlt]
  have hvl : 2^v ≤ w-2 := by omega
  have hpowge4 : 4 ≤ 2^v := by
    have hlim := two_mul_le_two_pow v hv
    omega
  have hw6 : 6 ≤ w := by omega
  have htwo_v : 2*v ≤ 2^v := two_mul_le_two_pow v hv
  have hvcoef : 2*v-3 ≤ w-5 := by omega
  have hpowbound : 2^(v+1) ≤ 2*(w-2) := by
    rw [pow_succ]
    omega
  let F : Nat := 2*dv+3*(2*w-3)
  have hFpos : 0<F := by
    dsimp [F]
    have h : 0<3*(2*w-3) := by omega
    omega
  have hFidentity : 2*Q+F = D*(2*w-3) := by
    have hstep : 2*Q+F=2*dw+3*(2*w-3) := by
      dsimp [F]
      omega
    calc
      2*Q+F = 2*dw+3*(2*w-3) := hstep
      _ = D*(2*w-3) := by
        dsimp [dw,D]
        rw [pow_succ]
        ring
  have hFdiv : D ∣ F := by
    have hDQ : D ∣ Q := ⟨t,ht⟩
    have h2Q : D ∣ 2*Q := ⟨2*t, by rw [ht]; ring⟩
    have hDF : D ∣ 2*Q+F := by
      rw [hFidentity]
      exact dvd_mul_right D _
    exact (Nat.dvd_add_iff_right h2Q).mpr hDF
  have hmulsmall : 2^(v+1)*(2*v-3) ≤
      (2*(w-2))*(w-5) := Nat.mul_le_mul hpowbound hvcoef
  have hFbound : F ≤ 2*(w-2)*(w-5)+6*w-9 := by
    have hf : F = 2^(v+1)*(2*v-3)+3*(2*w-3) := by
      dsimp [F,dv]
      rw [pow_succ]
      ring
    omega
  have hSq : 2*w*w ≤ 2^(w+1) := double_square_le_two_pow w hw6
  have hFsmall : F < D := by
    have ha : w-2+2=w := by omega
    have hb : w-5+5=w := by omega
    have hh : 6*w-9+9=6*w := by omega
    have hc : 2*(w-2)*(w-5)+6*w-9 < 2*w*w := by
      nlinarith
    dsimp [D]
    omega
  have hlow : D ≤ F := Nat.le_of_dvd hFpos hFdiv
  omega

#print axioms no_upward_division
end BB6.Agent20NoUpward
