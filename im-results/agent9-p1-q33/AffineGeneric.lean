import Lean
set_option maxHeartbeats 10000000
namespace BB6.Agent9Affine

theorem dvd_mul_any (d b r : Nat) (h : d∣b) : d∣b*r := by
  rcases h with ⟨k,hk⟩
  refine ⟨k*r, ?_⟩
  rw [hk]
  ac_rfl

theorem dvd_left_of_add (d a c : Nat) (hc:d∣c) (hs:d∣a+c) : d∣a := by
  exact (Nat.dvd_add_iff_left hc).mpr hs

theorem affine_div (k a b r v A B : Nat) (hk:0<k) (ha:a=k*A) (hb:b=2*k*B) (hd:a+b*r=k*v) :
  v=A+2*B*r := by
  apply Nat.mul_left_cancel hk
  calc
    k*v = a+b*r := hd.symm
    _ = k*(A+2*B*r) := by
      rw [ha,hb]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem affine_odd (L P m a b r t v zp k A B : Nat)
    (hk:0<k) (ha:a=k*A) (hb:b=2*k*B)
    (hd:a+b*r=k*v)
    (hn:2*zp+1=16*P*r+L+m+t+v) :
    (L+m+t+A)%2=1 := by
  have hv := affine_div k a b r v A B hk ha hb hd
  rw [hv] at hn
  have hnr : 2*zp+1 = 2*(8*P*r) + (L+m+t+A) + 2*(B*r) := by
    calc
      _ = 16*P*r+L+m+t+(A+2*B*r) := hn
      _ = 2*(8*P*r) + (L+m+t+A) + 2*(B*r) := by
        have h1 : 16*P*r = 2*(8*P*r) := by simp only [Nat.mul_assoc]; omega
        have h2 : 2*B*r = 2*(B*r) := by simp [Nat.mul_assoc]
        rw [h1,h2]
        omega
  omega

theorem affine_next (L P m a b r t v zp k A B : Nat)
    (hk:0<k) (ha:a=k*A) (hb:b=2*k*B)
    (hd:a+b*r=k*v)
    (hn:2*zp+1=16*P*r+L+m+t+v) :
    zp=(L+m+t+A)/2+(8*P+B)*r := by
  have hv := affine_div k a b r v A B hk ha hb hd
  have hodd := affine_odd L P m a b r t v zp k A B hk ha hb hd hn
  rw [hv] at hn
  have hbase : L+m+t+A=2*((L+m+t+A)/2)+1 := by
    have h := Nat.mod_add_div (L+m+t+A) 2
    omega
  have hlinear : 16*P*r+2*B*r=2*(8*P+B)*r := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hne : 2*zp+1 = (L+m+t+A) + 2*(8*P+B)*r := by
    calc
      _ = 16*P*r+L+m+t+(A+2*B*r) := hn
      _ = L+m+t+A + (16*P*r+2*B*r) := by omega
      _ = L+m+t+A + 2*(8*P+B)*r := by rw [hlinear]
  rw [hbase] at hne
  have hbassoc : 2*(8*P+B)*r = 2*((8*P+B)*r) := by simp [Nat.mul_assoc]
  rw [hbassoc] at hne
  omega

def decode (r : Nat) (nodes : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  nodes.map fun p => (p.1,p.2.1+p.2.2*r)

def check (L P : Nat) (nodes : List (Nat × Nat × Nat)) : Bool :=
  nodes.all fun p =>
    decide (p.1≤41 ∧ p.2.1%1024≠0 ∧ p.2.2%1024=0) &&
      (List.range 10).all (fun t => decide (
        p.2.1%2^t≠0 ∨
        (L+p.1+t+p.2.1/2^t)%2≠1 ∨
        (p.1+t+1, (L+p.1+t+p.2.1/2^t)/2,
          8*P+p.2.2/2^(t+1)) ∈ nodes))

theorem check_sound (L P : Nat) (nodes : List (Nat × Nat × Nat))
    (hc : check L P nodes = true) (r m z t v zp : Nat)
    (hm : (m,z)∈decode r nodes)
    (hdiv : z=2^t*v)
    (hn : 2*zp+1=16*P*r+L+m+t+v) :
    (m+t+1,zp)∈decode r nodes := by
  rcases List.mem_map.mp hm with ⟨⟨m0,a,b⟩,hmem,heq⟩
  change (m0,a+b*r)=(m,z) at heq
  have hmm : m0=m := (Prod.mk.inj heq).1
  have hzz : a+b*r=z := (Prod.mk.inj heq).2
  have hd : a+b*r=2^t*v := by rw [hzz]; exact hdiv
  subst m0
  subst z
  have hcheck := (List.all_eq_true.mp hc) (m,a,b) hmem
  have ⟨hbound,hsteps⟩ := Bool.and_eq_true_iff.mp hcheck
  have ⟨hmc,ham,hbm⟩ : m≤41 ∧ a%1024≠0 ∧ b%1024=0 :=
    of_decide_eq_true hbound
  have hb1024 : 1024∣b := Nat.dvd_iff_mod_eq_zero.mpr hbm
  have hbr1024 := dvd_mul_any 1024 b r hb1024
  have hz1024 : ¬1024∣a+b*r := by
    intro h
    have ha1024 := dvd_left_of_add 1024 a (b*r) hbr1024 h
    exact ham (Nat.dvd_iff_mod_eq_zero.mp ha1024)
  have ht : t<10 := by
    by_cases ht : t<10
    · exact ht
    have hdPow : 1024∣2^t := by
      have hd' := Nat.pow_dvd_pow 2 (show 10≤t by omega)
      simpa using hd'
    exact False.elim (hz1024 (Nat.dvd_trans hdPow ⟨v,hd⟩))
  have hbpow : 2^(t+1)∣b := by
    have hd : 2^(t+1)∣(1024:Nat) := by
      have hd' := Nat.pow_dvd_pow 2 (by omega : t+1≤10)
      simpa using hd'
    exact Nat.dvd_trans hd hb1024
  have hbpowt : 2^t∣b := by
    have hd : 2^t∣2^(t+1) := Nat.pow_dvd_pow 2 (by omega)
    exact Nat.dvd_trans hd hbpow
  have haz : 2^t∣a :=
    dvd_left_of_add (2^t) a (b*r) (dvd_mul_any (2^t) b r hbpowt) ⟨v,hd⟩
  have hmoda : a%2^t=0 := Nat.dvd_iff_mod_eq_zero.mp haz
  have hmodb : b%2^(t+1)=0 := Nat.dvd_iff_mod_eq_zero.mp hbpow
  have ha : a=2^t*(a/2^t) := by
    have h := Nat.mod_add_div a (2^t)
    omega
  have hb0 : b=2^(t+1)*(b/2^(t+1)) := by
    have h := Nat.mod_add_div b (2^(t+1))
    omega
  have hb : b=2*(2^t)*(b/2^(t+1)) := by
    simpa [Nat.pow_add_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb0
  have hodd := affine_odd L P m a b r t v zp (2^t) (a/2^t) (b/2^(t+1))
      (Nat.pow_pos (by decide)) ha hb hd hn
  have hnext := affine_next L P m a b r t v zp (2^t) (a/2^t) (b/2^(t+1))
      (Nat.pow_pos (by decide)) ha hb hd hn
  have hstepB := (List.all_eq_true.mp hsteps) t (List.mem_range.mpr ht)
  have hstep : a%2^t≠0 ∨ (L+m+t+a/2^t)%2≠1 ∨
      (m+t+1,(L+m+t+a/2^t)/2,8*P+b/2^(t+1)) ∈ nodes :=
    of_decide_eq_true hstepB
  rcases hstep with hbad | hbad | hgood
  · exact False.elim (hbad hmoda)
  · exact False.elim (hbad hodd)
  · apply List.mem_map.mpr
    refine ⟨(m+t+1,(L+m+t+a/2^t)/2,8*P+b/2^(t+1)),hgood,?_⟩
    change (m+t+1,(L+m+t+a/2^t)/2+(8*P+b/2^(t+1))*r)=(m+t+1,zp)
    simp only [Prod.mk.injEq, true_and]
    exact hnext.symm

theorem check_bounds (L P : Nat) (nodes : List (Nat × Nat × Nat))
    (hc : check L P nodes = true) (r m z : Nat)
    (hm : (m,z)∈decode r nodes) :
    m≤41 ∧ ¬1024∣z := by
  rcases List.mem_map.mp hm with ⟨⟨m0,a,b⟩,hmem,heq⟩
  change (m0,a+b*r)=(m,z) at heq
  have hmm : m0=m := (Prod.mk.inj heq).1
  have hzz : a+b*r=z := (Prod.mk.inj heq).2
  subst m0
  subst z
  have hcheck := (List.all_eq_true.mp hc) (m,a,b) hmem
  have hbound := (Bool.and_eq_true_iff.mp hcheck).1
  have ⟨hm41,ham,hbm⟩ : m≤41 ∧ a%1024≠0 ∧ b%1024=0 :=
    of_decide_eq_true hbound
  refine ⟨hm41, ?_⟩
  intro h
  have hb1024 : 1024∣b := Nat.dvd_iff_mod_eq_zero.mpr hbm
  have hbr1024 := dvd_mul_any 1024 b r hb1024
  have ha1024 := dvd_left_of_add 1024 a (b*r) hbr1024 h
  exact ham (Nat.dvd_iff_mod_eq_zero.mp ha1024)

#print axioms check_bounds
#print axioms check_sound

end BB6.Agent9Affine
