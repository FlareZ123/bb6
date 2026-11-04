import ChainWitnesses
set_option maxRecDepth 4096

namespace Audit

private theorem period_mod (m p r k : Nat) (hm : 1 < m) (hp : 2^p%m=1) :
    2^(r+p*k)%m=2^r%m := by
  have hpow : (2^p)^k %m=1 := by
    rw [Nat.pow_mod, hp]
    simp [Nat.mod_eq_of_lt hm]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hpow]
  simp

private theorem evenpow (n : Nat) : (2^(n+1))%2=0 := by
  rw [Nat.pow_succ]
  omega

private theorem period405 : 2^108 % 405 = 1 := by decide

private theorem r1218_mod_odd (k : Nat) : 2^(1218+4860*k) % 405 = 154 := by
  have heq : 1218+4860*k = 30+108*(11+45*k) := by omega
  rw [heq, period_mod 405 108 30 (11+45*k) (by omega) period405]

theorem r1218_mod (k : Nat) : 2^(1218+4860*k) % 810 = 154 := by
  have hodd := r1218_mod_odd k
  have he : 2^(1218+4860*k)%2=0 := by
    rw [show 1218+4860*k = (1217+4860*k)+1 by omega]
    exact evenpow (1217+4860*k)
  omega

/-- Two distinct incoming generic-source witnesses for every 1218-class power. -/
theorem fork1218 (k : Nat) :
    ∃ A B : Nat,
      GenericEdge A (2^(1218+4860*k)) ∧ GenericEdge B (2^(1218+4860*k)) ∧
      A ≠ B ∧ 15*A+2=8*2^(1218+4860*k) ∧
      81*B+68=32*2^(1218+4860*k) ∧
      10 < A ∧ A < 2^(1218+4860*k) ∧
      10 < B ∧ B < 2^(1218+4860*k) := by
  let R := 2^(1218+4860*k)
  have hmod : R % 810 = 154 := r1218_mod k
  let q := R / 810
  have hR : R = 810*q+154 := by
    have hh := Nat.mod_add_div R 810
    omega
  let v1 := 216*q+41
  let v2 := 80*q+15
  let u1 := 270*q+51
  let u2 := 90*q+17
  let A := 2*v1
  let B := 4*v2
  have hfirst : GenericEdge A R := by
    refine ⟨1,1,v1,u1,by omega,by dsimp [v1]; omega,?_,?_,?_,?_,?_⟩
    all_goals omega
  have hsecond : GenericEdge B R := by
    refine ⟨2,2,v2,u2,by omega,by dsimp [v2]; omega,?_,?_,?_,?_,?_⟩
    all_goals omega
  refine ⟨A,B,hfirst,hsecond,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [A,B,v1,v2]; omega

#print axioms fork1218
end Audit
