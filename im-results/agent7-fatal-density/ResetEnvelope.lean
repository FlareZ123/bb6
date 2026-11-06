import FirstInverseComplete
set_option maxHeartbeats 0
namespace CascadeInverseMetric
open CascadeResetInverse

/-- Exact even-arm inverse edges increase the reset height by at least
    k+3, where k is the unique failed-sweep scale. -/
theorem even_arm_gap (h u k:Nat)
  (hb:6*2^k-1≤u ∧ u≤8*2^k-3)
  (he:2*u=8*2^k+h+k) :
    h+k+3≤u := by
  have hp:0<2^k:=Nat.one_le_pow k 2 (by decide)
  omega

/-- Any odd inverse arm contracts the height by an optimal factor 2/3
    with a scale-indexed additive gap, at every 3-adic drain length. -/
theorem odd_arm_gap (h u k t d:Nat)
  (hb:6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1)
  (hz:2*u+5=3^(t+1)*d)
  (he:2*(2^t*d)=8*2^k+h+k+5):
    3*h+3*k+13≤2*u := by
  have hpow:2^t≤3^t:=Nat.pow_le_pow_left (by decide) t
  have hprod:3*(2^t*d)≤3^(t+1)*d:=by
    calc
      3*(2^t*d)≤3*(3^t*d):=Nat.mul_le_mul_left 3
        (Nat.mul_le_mul_right d hpow)
      _=3^(t+1)*d:=by rw[Nat.pow_succ];ac_rfl
  omega

/-- A stronger valuation-specific contraction with exact dyadic scale
    and the exact odd drain exponent t. -/
theorem odd_arm_scaled_gap (h u k t d:Nat)
  (hb:6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1)
  (hz:2*u+5=3^(t+1)*d)
  (he:2*(2^t*d)=8*2^k+h+k+5):
    3^(t+1)*(h+k+6)≤2^t*(2*u+5) := by
  have hq:h+k+6≤2^t*d:=by omega
  calc
    3^(t+1)*(h+k+6)≤3^(t+1)*(2^t*d):=
      Nat.mul_le_mul_left _ hq
    _=2^t*(3^(t+1)*d):=by ac_rfl
    _=2^t*(2*u+5):=by rw[←hz]

/-- Complete source-exact disjunction of sharp forward reset growth
    conditions; does not suppose that the parent belongs to the blank orbit. -/
theorem parent_envelope (h u:Nat) (hp:ResetParent h u):
  (∃k, h+k+3≤u) ∨ (∃k t, 3*h+3*k+13≤2*u ∧
    3^(t+1)*(h+k+6)≤2^t*(2*u+5)) := by
  rcases hp with ⟨k,hb,he⟩ | ⟨k,t,d,hd,hb,hz,he⟩
  · exact Or.inl ⟨k,even_arm_gap h u k hb he⟩
  · exact Or.inr ⟨k,t,odd_arm_gap h u k t d hb hz he,
      odd_arm_scaled_gap h u k t d hb hz he⟩

private theorem k_bound (k:Nat):k+7≤8*2^k:=by
  induction k with
  | zero=>decide
  | succ k ih=>
    rw[Nat.pow_succ]
    omega

/-- Sharpness: the even-arm gap k+3 is attained at every scale k. -/
theorem even_gap_sharp (k:Nat):
  ∃ h u, ResetParent h u ∧ h+k+3=u := by
  let p:=2^k
  let h:=8*p-k-6
  let u:=8*p-3
  have hk:=k_bound k
  have hb:6*p-1≤u ∧ u≤8*p-3:=by
    dsimp[u]
    have hp:0<p:=Nat.one_le_pow k 2 (by decide)
    omega
  have he:2*u=8*p+h+k:=by dsimp[u,h];omega
  refine ⟨h,u,Or.inl ⟨k,by simpa [p] using hb,
    by simpa [p] using he⟩,?_⟩
  dsimp[h,u]
  omega

/-- Sharpness: 3h+3k+13=2u is attained by a legitimate odd arm at
    every dyadic scale k. -/
theorem odd_gap_sharp (k:Nat):
  ∃ h u, ResetParent h u ∧ 3*h+3*k+13=2*u := by
  let p:=2^k
  let h:=8*p-k-7
  let u:=12*p-4
  have hk:=k_bound k
  have hb:6*p+1≤8*p-1 ∧ 8*p-1≤8*p-1:=by
    have hp:0<p:=Nat.one_le_pow k 2 (by decide)
    omega
  have he:2*(8*p-1)=8*p+h+k+5:=by dsimp[h];omega
  have hz:2*u+5=3*(8*p-1):=by dsimp[u];omega
  refine ⟨h,u,Or.inr ⟨k,0,8*p-1,?_,?_,?_,?_⟩,?_⟩
  · have hp:0<p:=Nat.one_le_pow k 2 (by decide)
    omega
  · simpa [p] using hb
  · simpa using hz
  · simpa [p] using he
  · dsimp[h,u];omega

#print axioms parent_envelope
#print axioms even_gap_sharp
#print axioms odd_gap_sharp
end CascadeInverseMetric
