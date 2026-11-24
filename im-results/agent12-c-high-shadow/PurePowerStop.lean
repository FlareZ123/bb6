import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12PurePower

private theorem neg_product_mod (P a : Nat) (ha : 1≤a) (hA : a≤P) :
    (P*a)%(P+1)=P+1-a := by
  have h1 : P*a=(P+1)*(a-1)+(P+1-a) := by
    have h2 : (P+1)*(a-1+1)=(P+1)*(a-1)+(P+1) := by rw [Nat.mul_add,Nat.mul_one]
    rw [show a-1+1=a by omega,Nat.add_mul,Nat.one_mul] at h2
    omega
  rw [h1,Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Exact powers of two modulo 2^b+1, with no bound on the exponent. -/
theorem block_residue (P q : Nat) (hP : 1≤P) :
    P^q%(P+1)=if q%2=0 then 1 else P := by
  induction q with
  | zero => simp [Nat.mod_eq_of_lt (show 1<P+1 by omega)]
  | succ q ih =>
    rw [Nat.pow_succ,Nat.mul_mod,ih,Nat.mod_eq_of_lt (show P<P+1 by omega)]
    by_cases h : q%2=0
    · rw [ite_eq_left h,ite_eq_right (show (q+1)%2≠0 by omega),Nat.one_mul]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [ite_eq_right h,ite_eq_left (show (q+1)%2=0 by omega),neg_product_mod P P hP (by omega)]
      omega

theorem power_residue (b v : Nat) (hb : 1≤b) :
    2^v%(2^b+1)=if (v/b)%2=0 then 2^(v%b) else 2^b+1-2^(v%b) := by
  let P := 2^b
  let q := v/b
  let r := v%b
  have hr : r<b := Nat.mod_lt _ (by omega)
  have hP : 1≤P := Nat.pow_pos (by decide)
  have ha : 1≤2^r := Nat.pow_pos (by decide)
  have haP : 2^r<P := Nat.pow_lt_pow_right (by decide) hr
  have hv : v=b*q+r := by simpa [q,r,Nat.add_comm] using (Nat.mod_add_div v b).symm
  have hpow : 2^v=P^q*2^r := by rw [hv,Nat.pow_add,←Nat.pow_mul]
  change 2^v%(P+1)=if q%2=0 then 2^r else P+1-2^r
  rw [hpow,Nat.mul_mod,block_residue P q hP,Nat.mod_eq_of_lt (show 2^r<P+1 by omega)]
  split
  · rw [Nat.one_mul]; exact Nat.mod_eq_of_lt (by omega)
  · exact neg_product_mod P (2^r) ha (by omega)

/-- A small positive additive complement of a power modulo a Fermat-type
    denominator must itself be a power, in the negative half-cycle. -/
theorem small_complement (b v c : Nat) (hb : 1≤b) (hc : 1≤c)
    (hsmall : c≤2^(b-1)) (hd : 2^b+1∣2^v+c) :
    (v/b)%2=1 ∧ c=2^(v%b) := by
  have h := power_residue b v hb
  have hr : v%b<b := Nat.mod_lt _ (by omega)
  have hr' : v%b≤b-1 := by omega
  have hbound : 2^(v%b)≤2^(b-1) := Nat.pow_le_pow_right (by decide) hr'
  have hhalf : 2^b=2*2^(b-1) := by
    calc
      2^b = 2^((b-1)+1) := by congr 1; omega
      _ = 2*2^(b-1) := by rw [Nat.pow_succ,Nat.mul_comm]
  have hcp : c<2^b+1 := by omega
  have hpos : 1≤2^(v%b) := Nat.pow_pos (by decide)
  have hmod := Nat.mod_eq_zero_of_dvd hd
  rw [Nat.add_mod,h,Nat.mod_eq_of_lt hcp] at hmod
  by_cases hq : (v/b)%2=0
  · rw [ite_eq_left hq] at hmod
    have hlt : 2^(v%b)+c<2^b+1 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hmod
    omega
  · rw [ite_eq_right hq] at hmod
    have hlo : 0<2^b+1-2^(v%b)+c := by omega
    have hhi : 2^b+1-2^(v%b)+c<2*(2^b+1) := by omega
    obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hk1 : k=1 := by
      by_cases hz : k=0
      · subst k; omega
      · by_cases h1 : k=1
        · exact h1
        · have hmul := Nat.mul_le_mul_left (2^b+1) (show 2≤k by omega)
          omega
    rw [hk1,Nat.mul_one] at hk
    omega

private theorem complement_bound (m : Nat) (hm : 1≤m) : 3*m+5≤2^(2*m+1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : m=0
    · subst m; decide
    · have hh := ih (by omega)
      rw [show 2*(m+1)+1=2*m+1+2 by omega,Nat.pow_add]
      change 3*(m+1)+5≤2^(2*m+1)*4
      omega

/-- Complete necessary arithmetic restriction on a pure-power rounded
    sum at an authentic high stopping target. -/
theorem high_stop_pure_power (j m k v : Nat) (hm : 1≤m)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hpow : 2*j+3+k+(2*j+3+k)%2=2^v) :
    let b := 2*m+2
    let o := (j+m)%2
    let r := v%b
    (v/b)%2=1 ∧ 2^r+o=3*m+5 ∧ r<b ∧
      (2^b+1)*(j+3)=2^v+2^r := by
  dsimp
  let b := 2*m+2
  let P := 2^b
  let o := (j+m)%2
  let c := 3*m+5-o
  have hP2 : P%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1≤b))
  have hPP : (P*(j+3))%2=0 := by rw [Nat.mul_mod,hP2]; simp
  change k+j+3*m+5=P*(j+3) at hstop
  have ho : (2*j+3+k)%2=o := by dsimp [o]; omega
  rw [ho] at hpow
  have hC : (P+1)*(j+3)=2^v+c := by
    rw [Nat.add_mul,Nat.one_mul]
    dsimp [c]
    omega
  have hc : 1≤c := by dsimp [c,o]; omega
  have hsmall : c≤2^(b-1) := by
    have hh := complement_bound m hm
    have he : b-1=2*m+1 := by dsimp [b]
    rw [he]
    dsimp [c]; omega
  obtain ⟨hq,hr⟩ := small_complement b v c (by omega) hc hsmall ⟨j+3,hC.symm⟩
  change (v/b)%2=1 ∧ 2^(v%b)+o=3*m+5 ∧ v%b<b ∧ (P+1)*(j+3)=2^v+2^(v%b)
  exact ⟨hq,by dsimp [c] at hr; omega,Nat.mod_lt _ (by omega),by rw [←hr]; exact hC⟩

/-- On the stopping equation the arithmetic restriction is also sufficient. -/
theorem high_stop_pure_power_iff (j m k v : Nat) (hm : 1≤m)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3+k+(2*j+3+k)%2=2^v) ↔
      ((v/(2*m+2))%2=1 ∧ 2^(v%(2*m+2))+(j+m)%2=3*m+5 ∧
        (2^(2*m+2)+1)*(j+3)=2^v+2^(v%(2*m+2))) := by
  constructor
  · intro h
    have hh := high_stop_pure_power j m k v hm hstop h
    exact ⟨hh.1,hh.2.1,hh.2.2.2⟩
  · rintro ⟨_,hc,hprod⟩
    have hP2 : 2^(2*m+2)%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1≤2*m+2))
    have hPP : (2^(2*m+2)*(j+3))%2=0 := by rw [Nat.mul_mod,hP2]; simp
    rw [Nat.add_mul,Nat.one_mul] at hprod
    omega

private theorem pow2_min (r : Nat) (hr : 3≤r) : 2*r+2≤(2:Nat)^r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases h : r<3
    · have hr2 : r=2 := by omega
      subst r; decide
    · have hh := ih (by omega)
      rw [Nat.pow_succ]
      omega

/-- The exponent r determines m; the remaining high index is determined
    by a single odd multiple of b. This is a sparse two-exponent family,
    not an assertion that any member is reachable. -/
theorem high_power_exponent_form (j m k v : Nat) (hm : 1≤m)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hpow : 2*j+3+k+(2*j+3+k)%2=2^v) :
    ∃ r s : Nat, 3≤r ∧
      2^r+(1-r%2)=3*m+5 ∧
      (j+m)%2=1-r%2 ∧
      v=(2*m+2)*(2*s+1)+r ∧
      (2^(2*m+2)+1)*(j+3)=2^v+2^r := by
  let b := 2*m+2
  let r := v%b
  let s := (v/b)/2
  have hh := high_stop_pure_power j m k v hm hstop hpow
  change (v/b)%2=1 ∧ 2^r+(j+m)%2=3*m+5 ∧ r<b ∧ (2^b+1)*(j+3)=2^v+2^r at hh
  obtain ⟨hq,hc,hr,hprod⟩ := hh
  have hr3 : 3≤r := by
    by_cases h : 3≤r
    · exact h
    · have hb : 2^r≤(2:Nat)^2 := Nat.pow_le_pow_right (by decide) (by omega)
      change 2^r≤4 at hb
      omega
  have hrmod := block_residue 2 r (by decide)
  change 2^r%3=(if r%2=0 then 1 else 2) at hrmod
  have ho : (j+m)%2=1-r%2 := by
    by_cases h : r%2=0 <;> simp only [h,ite_true,ite_false] at hrmod <;> omega
  have hqform : v/b=2*s+1 := by dsimp [s]; omega
  have hv := Nat.mod_add_div v b
  rw [hqform] at hv
  refine ⟨r,s,hr3,?_,ho,?_,hprod⟩
  · omega
  · change v=b*(2*s+1)+r
    dsimp [r] at hv ⊢
    omega

private theorem low_linear_bound (m : Nat) : 4*m+4≤(2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)+2=2*m+2+2 by omega,Nat.pow_add]
    change 4*(m+1)+4≤2^(2*m+2)*4
    omega

/-- No low stopping target has a pure-power rounded sum, including m=0. -/
theorem low_stop_not_pure_power (m k v : Nat)
    (hstop : k+3*m+4=2^(2*m+3)) : 1+k+(1+k)%2≠2^v := by
  intro he
  have hhi : 1+k+(1+k)%2<2^(2*m+3) := by omega
  have hlo : 2^(2*m+2)<1+k+(1+k)%2 := by
    have hh := low_linear_bound m
    have hp : (2:Nat)^(2*m+3)=2^(2*m+2)*2 := by rw [show 2*m+3=2*m+2+1 by omega,Nat.pow_succ]
    rw [hp] at hstop
    omega
  rw [he] at hhi hlo
  by_cases hv : v≤2*m+2
  · have h := Nat.pow_le_pow_right (by decide : 0<2) hv
    omega
  · have h := Nat.pow_le_pow_right (by decide : 0<2) (show 2*m+3≤v by omega)
    omega

/-- Every exponent pair in the displayed sparse family occurs as a
    genuine arithmetic stopping target (whether reachable remains open). -/
def familyM (r : Nat) : Nat := (2^r+(1-r%2)-5)/3
def familyV (r s : Nat) : Nat := (2*familyM r+2)*(2*s+1)+r
def familyJ (r s : Nat) : Nat := (2^(familyV r s)+2^r)/(2^(2*familyM r+2)+1)-3
def familyK (r s : Nat) : Nat := 2^(2*familyM r+2)*(familyJ r s+3)-(familyJ r s+3*familyM r+5)

theorem family_exact (r s : Nat) (hr : 3≤r) :
    let m := familyM r
    let v := familyV r s
    let j := familyJ r s
    let k := familyK r s
    1≤m ∧ k+j+3*m+5=2^(2*m+2)*(j+3) ∧
      2*j+3+k+(2*j+3+k)%2=2^v := by
  dsimp only
  let m := familyM r
  let b := 2*m+2
  let P := 2^b
  let v := familyV r s
  let T := 2^v+2^r
  let J := T/(P+1)
  let j := J-3
  let k := P*(j+3)-(j+3*m+5)
  change 1≤m ∧ k+j+3*m+5=P*(j+3) ∧ 2*j+3+k+(2*j+3+k)%2=2^v
  have hr2 := pow2_min r hr
  have hmod := block_residue 2 r (by decide)
  change 2^r%3=(if r%2=0 then 1 else 2) at hmod
  have hc : 2^r+(1-r%2)=3*m+5 := by
    dsimp [m,familyM]
    by_cases h : r%2=0 <;> simp only [h,ite_true,ite_false] at hmod <;> omega
  have hm : 1≤m := by omega
  have hrb : r<b := by dsimp [b]; omega
  have hv : v=b*(2*s+1)+r := rfl
  have hb : 0<b := by dsimp [b]; omega
  have hvr : v%b=r := by rw [hv,Nat.mul_add_mod,Nat.mod_eq_of_lt hrb]
  have hvq : v/b=2*s+1 := by rw [hv,Nat.mul_add_div hb,Nat.div_eq_of_lt hrb,Nat.add_zero]
  have hP : 1≤P := Nat.pow_pos (by decide)
  have hpow := power_residue b v (by omega)
  change 2^v%(P+1)=if (v/b)%2=0 then 2^(v%b) else P+1-2^(v%b) at hpow
  rw [hvq,hvr,ite_eq_right (show (2*s+1)%2≠0 by omega)] at hpow
  have hrP : 2^r<P := Nat.pow_lt_pow_right (by decide) hrb
  have hT : P+1∣T := by
    apply Nat.dvd_of_mod_eq_zero
    dsimp [T]
    rw [Nat.add_mod,hpow,Nat.mod_eq_of_lt (show 2^r<P+1 by omega)]
    have hh : P+1-2^r+2^r=P+1 := by omega
    rw [hh,Nat.mod_self]
  have hJ : (P+1)*J=T := by dsimp [J]; rw [Nat.mul_comm,Nat.div_mul_cancel hT]
  have hbig : P*2^r≤2^v := by
    have hh : b+r≤v := by
      have h := Nat.mul_le_mul_left b (show 1≤2*s+1 by omega)
      rw [Nat.mul_one] at h
      omega
    have h := Nat.pow_le_pow_right (by decide : 0<2) hh
    rw [Nat.pow_add] at h
    exact h
  have hTbig : (P+1)*2^r≤T := by rw [Nat.add_mul,Nat.one_mul]; dsimp [T]; omega
  have hJbig : 2^r≤J := Nat.le_of_mul_le_mul_left (by rwa [hJ]) (by omega)
  have hj : j+3=J := by dsimp [j]; omega
  have hprod : (P+1)*(j+3)=2^v+2^r := by rw [hj,hJ]
  have hPlin : 4*m+4≤P := low_linear_bound m
  have hPj : j≤P*j := by simpa using Nat.mul_le_mul_right j hP
  have hstop_bound : j+3*m+5≤P*(j+3) := by rw [Nat.mul_add]; omega
  have hs : k+j+3*m+5=P*(j+3) := by dsimp [k]; omega
  have hP2 : P%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1≤b))
  have hv2 : 2^v%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1≤v))
  have hr2' : 2^r%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1≤r))
  have hPP : (P*(j+3))%2=0 := by rw [Nat.mul_mod,hP2]; simp
  have hJodd : j%2=1 := by rw [Nat.add_mul,Nat.one_mul] at hprod; omega
  have ho : (j+m)%2=1-r%2 := by omega
  have hf : 2^(v%b)+(j+m)%2=3*m+5 := by rw [hvr,ho]; exact hc
  have hq : (v/b)%2=1 := by rw [hvq]; omega
  exact ⟨hm,hs,(high_stop_pure_power_iff j m k v hm hs).mpr ⟨hq,hf,by change (P+1)*(j+3)=2^v+2^(v%b); rw [hvr]; exact hprod⟩⟩

/-- Conversely every positive-index pure-power stopping target occurs in
    the explicit two-exponent construction. -/
theorem high_power_family_complete (j m k v : Nat) (hm : 1≤m)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp : 2*j+3+k+(2*j+3+k)%2=2^v) :
    ∃ r s : Nat, 3≤r ∧ m=familyM r ∧ v=familyV r s ∧ j=familyJ r s ∧ k=familyK r s := by
  obtain ⟨r,s,hr,hc,_,hv,hprod⟩ := high_power_exponent_form j m k v hm hstop hp
  have hm' : m=familyM r := by unfold familyM; omega
  have hv' : v=familyV r s := by unfold familyV; rw [←hm']; exact hv
  have hj' : j=familyJ r s := by
    unfold familyJ
    rw [←hv',←hm',←hprod,Nat.mul_div_cancel_left _ (by have h : 0<2^(2*m+2) := Nat.pow_pos (by decide); omega)]
    omega
  have hk' : k=familyK r s := by
    unfold familyK
    rw [←hm',←hj']
    omega
  exact ⟨r,s,hr,hm',hv',hj',hk'⟩

/-- The m=0 boundary has a different small-complement range, but is
    still exactly a single exponential progression. -/
theorem high_zero_power_iff (j k v : Nat) (hstop : k+j+5=4*(j+3)) :
    (2*j+3+k+(2*j+3+k)%2=2^v) ↔
      (4≤v ∧ v%4=0 ∧ 5*(j+3)=2^v+4) := by
  constructor
  · intro hp
    let o := j%2
    have ho : (2*j+3+k)%2=o := by dsimp [o]; omega
    have hprod : 5*(j+3)=2^v+(5-o) := by rw [ho] at hp; omega
    have hv4 : 4≤v := by
      by_cases h : 4≤v
      · exact h
      · have hle : 2^v≤(2:Nat)^3 := Nat.pow_le_pow_right (by decide) (by omega)
        change 2^v≤8 at hle
        omega
    have hr := power_residue 2 v (by decide)
    change 2^v%5=(if (v/2)%2=0 then 2^(v%2) else 5-2^(v%2)) at hr
    have hpow : 2^(v%2)=(if v%2=0 then 1 else 2) := by
      by_cases h : v%2=0
      · simp [h]
      · have h1 : v%2=1 := by omega
        simp [h1]
    rw [hpow] at hr
    have hvmod : v%4=0 ∧ o=1 := by
      by_cases h1 : (v/2)%2=0 <;> by_cases h2 : v%2=0 <;>
        simp only [h1,h2,ite_true,ite_false] at hr <;> omega
    exact ⟨hv4,hvmod.1,by omega⟩
  · rintro ⟨hv,_,hprod⟩
    have he : 2^v%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1≤v))
    omega

#print axioms power_residue
#print axioms small_complement
#print axioms high_stop_pure_power
#print axioms high_stop_pure_power_iff
#print axioms high_power_exponent_form
#print axioms low_stop_not_pure_power
#print axioms family_exact
#print axioms high_power_family_complete
#print axioms high_zero_power_iff
end BB6.Agent12PurePower
