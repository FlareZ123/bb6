import Lean
set_option maxHeartbeats 2000000

namespace BB6.Precision

theorem odd_base (a c z : Nat) (h : 2*z+1=a+2*c) :
    ∃ u, 2*u+1=a := by
  have : a%2=1 := by omega
  refine ⟨a/2, ?_⟩
  omega

theorem two_pow_dvd_of_le (a b : Nat) (h : a≤b) :
    (2:Nat)^a ∣ 2^b := Nat.pow_dvd_pow 2 h

theorem cancel_two_pow (t x y : Nat)
    (h : 2^t*x=2^t*y) : x=y := by
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) h

/-- A lifted scalar node's depth is bounded by the nondivisibility of
    its base shadow coordinate, uniformly in every natural perturbation. -/
theorem depth_lt_K
    (K M m z0 s t v : Nat)
    (hm : m≤M)
    (hnodiv : ¬2^K ∣ z0)
    (hd : z0+2^(K+M-m)*s=2^t*v) : t<K := by
  by_cases hlt : t<K
  · exact hlt
  exfalso
  have ht' : K≤t := by omega
  have he : K≤K+M-m := by omega
  have hKdiv : 2^K ∣ 2^(K+M-m)*s := by
    rcases Nat.pow_dvd_pow 2 he with ⟨a,ha⟩
    refine ⟨a*s, ?_⟩
    rw [ha]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hKright : 2^K ∣ 2^t*v := by
    rcases Nat.pow_dvd_pow 2 ht' with ⟨a,ha⟩
    refine ⟨a*v, ?_⟩
    rw [ha]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hKsum : 2^K ∣ z0+2^(K+M-m)*s := by
    rw [hd]
    exact hKright
  exact hnodiv ((Nat.dvd_add_iff_left hKdiv).mpr hKsum)

/-- Cost-dependent 2-adic precision is propagated by a scalar dyadic inverse
    edge. The conclusion assumes the target base cost stays within M; the
    caller also supplies the edge-depth bound t<K. The separate base graph
    closure supplies the target cost bound after this lemma constructs its
    necessary base predecessor. -/
theorem precision_step
    (K M L0 r m z0 s t v zp : Nat)
    (hm : m≤M) (ht : t<K)
    (hdiv : z0+2^(K+M-m)*s=2^t*v)
    (hn : 2*zp+1=16*2^(K+M)*r+L0+m+t+v) :
    ∃ v0 z0' s',
      z0=2^t*v0 ∧
      2*z0'+1=L0+m+t+v0 ∧
      zp=z0'+2^(K+M-(m+t+1))*s' ∧
      s'=s+8*2^(m+t+1)*r := by
  let e := K+M-(m+t+1)
  have hpow : (2:Nat)^(K+M-m) = 2^t*(2*2^e) := by
    have heq : K+M-m=t+1+e := by dsimp [e]; omega
    rw [heq, Nat.pow_add, Nat.pow_add]
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hbigpow : (16:Nat)*2^(K+M)*r =
      2*(2^e)*(8*2^(m+t+1)*r) := by
    have heq : K+M=e+(m+t+1) := by dsimp [e]; omega
    rw [heq, Nat.pow_add]
    simp only [show (16:Nat)=2*8 by decide,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hshift : 2*(2^e*(s+8*2^(m+t+1)*r)) =
      2*2^e*s + 2*2^e*(8*2^(m+t+1)*r) := by
    simp [Nat.mul_add, Nat.mul_assoc]
  have hdiv0 : 2^t∣z0 := by
    have hsd : 2^t ∣ 2^(K+M-m)*s := by
      rw [hpow]
      exact ⟨2*2^e*s, by simp [Nat.mul_comm, Nat.mul_left_comm]⟩
    have htot : 2^t∣z0+2^(K+M-m)*s := by
      rw [hdiv]
      exact ⟨v, rfl⟩
    exact (Nat.dvd_add_iff_left hsd).mpr htot
  obtain ⟨v0,hv0⟩ := hdiv0
  have hv : v=v0+2*2^e*s := by
    have hh : (2:Nat)^t*(v0+2*2^e*s) = 2^t*v := by
      calc
        _ = 2^t*v0 + (2^t*(2*2^e))*s := by
          simp [Nat.mul_add, Nat.mul_assoc]
        _ = z0+2^(K+M-m)*s := by rw [hv0, hpow]
        _ = 2^t*v := hdiv
    exact (cancel_two_pow t (v0+2*2^e*s) v hh).symm
  have hodd : ∃ z0', 2*z0'+1 = L0+m+t+v0 := by
    have hh : 2*zp+1 =
        (L0+m+t+v0)+2*(2^e*(s+8*2^(m+t+1)*r)) := by
      rw [hv, hbigpow] at hn
      omega
    exact odd_base _ _ _ hh
  rcases hodd with ⟨z0',hz0'⟩
  refine ⟨v0,z0',s+8*2^(m+t+1)*r, hv0, hz0', ?_, rfl⟩
  change zp = z0'+ 2^e*(s+8*2^(m+t+1)*r)
  have hh : 2*zp+1=2*z0'+1+2*(2^e*(s+8*2^(m+t+1)*r)) := by
    rw [hv, hbigpow] at hn
    omega
  omega

#print axioms depth_lt_K
#print axioms precision_step
end BB6.Precision
