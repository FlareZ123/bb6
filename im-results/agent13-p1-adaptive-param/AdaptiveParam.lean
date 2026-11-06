import AffineAdaptive
set_option maxHeartbeats 10000000
namespace BB6.Agent13AdaptiveParam
open BB6.Agent9Affine
open BB6.Agent9Adaptive (project decode)

def check (K B L P : Nat) (nodes : List (Nat×Nat×Nat×Nat)) : Bool :=
  nodes.all fun p =>
    decide (p.1≤B ∧ 0<p.2.2.2 ∧ p.2.2.2≤K ∧
      p.2.1%2^p.2.2.2≠0 ∧ p.2.2.1%2^p.2.2.2=0) &&
    (List.range K).all fun t => decide (
      p.2.2.2≤t ∨ p.2.1%2^t≠0 ∨
      (L+p.1+t+p.2.1/2^t)%2≠1 ∨
      (p.1+t+1,(L+p.1+t+p.2.1/2^t)/2,
         8*P+p.2.2.1/2^(t+1)) ∈ project nodes)

theorem check_sound (K B L P : Nat) (nodes : List (Nat×Nat×Nat×Nat))
    (hc : check K B L P nodes = true) (r m z t v zp : Nat)
    (hm : (m,z)∈decode r nodes)
    (hdiv : z=2^t*v)
    (hn : 2*zp+1=16*P*r+L+m+t+v) :
    (m+t+1,zp)∈decode r nodes := by
  rcases List.mem_map.mp hm with ⟨⟨m0,a,b,k⟩,hmem,heq⟩
  change (m0,a+b*r)=(m,z) at heq
  have hmm : m0=m := (Prod.mk.inj heq).1
  have hzz : a+b*r=z := (Prod.mk.inj heq).2
  have hd : a+b*r=2^t*v := by rw [hzz]; exact hdiv
  subst m0
  subst z
  have hcheck := (List.all_eq_true.mp hc) (m,a,b,k) hmem
  have ⟨hbound,hsteps⟩ := Bool.and_eq_true_iff.mp hcheck
  have ⟨hmc,hkpos,hkmax,ham,hbm⟩ :
    m≤B ∧ 0<k ∧ k≤K ∧ a%2^k≠0 ∧ b%2^k=0 :=
    of_decide_eq_true hbound
  have hbK : 2^k∣b := Nat.dvd_iff_mod_eq_zero.mpr hbm
  have hbrK := dvd_mul_any (2^k) b r hbK
  have hzK : ¬2^k∣a+b*r := by
    intro h
    have haK := dvd_left_of_add (2^k) a (b*r) hbrK h
    exact ham (Nat.dvd_iff_mod_eq_zero.mp haK)
  have ht : t<k := by
    by_cases h : t<k
    · exact h
    have hdivK : 2^k∣2^t := Nat.pow_dvd_pow 2 (by omega)
    exact False.elim (hzK (Nat.dvd_trans hdivK ⟨v,hd⟩))
  have hbpow : 2^(t+1)∣b := by
    have hs : 2^(t+1)∣2^k := Nat.pow_dvd_pow 2 (by omega)
    exact Nat.dvd_trans hs hbK
  have hbpowt : 2^t∣b := by
    have hs : 2^t∣2^(t+1) := Nat.pow_dvd_pow 2 (by omega)
    exact Nat.dvd_trans hs hbpow
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
  have hstepB := (List.all_eq_true.mp hsteps) t (List.mem_range.mpr (by omega : t<K))
  have hstep : k≤t ∨ a%2^t≠0 ∨ (L+m+t+a/2^t)%2≠1 ∨
    (m+t+1,(L+m+t+a/2^t)/2,8*P+b/2^(t+1))∈project nodes :=
    of_decide_eq_true hstepB
  rcases hstep with hbad | hbad | hbad | hgood
  · omega
  · exact False.elim (hbad hmoda)
  · exact False.elim (hbad hodd)
  · rcases List.mem_map.mp hgood with ⟨⟨m1,a1,b1,k1⟩,hmem1,heq1⟩
    change (m1,a1,b1)=(m+t+1,(L+m+t+a/2^t)/2,8*P+b/2^(t+1)) at heq1
    have hm1 : m1=m+t+1 := (Prod.mk.inj heq1).1
    have ha1 : a1=(L+m+t+a/2^t)/2 := (Prod.mk.inj (Prod.mk.inj heq1).2).1
    have hb1 : b1=8*P+b/2^(t+1) := (Prod.mk.inj (Prod.mk.inj heq1).2).2
    apply List.mem_map.mpr
    refine ⟨(m1,a1,b1,k1),hmem1,?_⟩
    change (m1,a1+b1*r)=(m+t+1,zp)
    rw [hm1,ha1,hb1,hnext]

theorem check_bounds (K B L P : Nat) (nodes : List (Nat×Nat×Nat×Nat))
    (hc : check K B L P nodes = true) (r m z : Nat)
    (hm : (m,z)∈decode r nodes) :
    m≤B ∧ ¬2^K∣z := by
  rcases List.mem_map.mp hm with ⟨⟨m0,a,b,k⟩,hmem,heq⟩
  change (m0,a+b*r)=(m,z) at heq
  have hmm : m0=m := (Prod.mk.inj heq).1
  have hzz : a+b*r=z := (Prod.mk.inj heq).2
  subst m0
  subst z
  have hcheck := (List.all_eq_true.mp hc) (m,a,b,k) hmem
  have hbound := (Bool.and_eq_true_iff.mp hcheck).1
  have ⟨hmB,hkpos,hkmax,ham,hbm⟩ :
    m≤B ∧ 0<k ∧ k≤K ∧ a%2^k≠0 ∧ b%2^k=0 :=
    of_decide_eq_true hbound
  refine ⟨hmB, ?_⟩
  intro h
  have hbK : 2^k∣b := Nat.dvd_iff_mod_eq_zero.mpr hbm
  have hbrK := dvd_mul_any (2^k) b r hbK
  have haK : 2^k∣2^K := Nat.pow_dvd_pow 2 hkmax
  have hzk : 2^k∣a+b*r := Nat.dvd_trans haK h
  have haz := dvd_left_of_add (2^k) a (b*r) hbrK hzk
  exact ham (Nat.dvd_iff_mod_eq_zero.mp haz)

#print axioms check_sound
#print axioms check_bounds
end BB6.Agent13AdaptiveParam
