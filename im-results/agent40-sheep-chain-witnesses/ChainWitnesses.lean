import Std
set_option maxRecDepth 4096

namespace Audit

private theorem pow_mod_period (m period r k : Nat)
    (hm : 1 < m) (hp : 2^period % m = 1) :
    2^(r + period*k) % m = 2^r % m := by
  have hpow : (2^period)^k % m = 1 := by
    rw [Nat.pow_mod, hp]
    simp [Nat.mod_eq_of_lt hm]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hpow]
  simp

private theorem period1485 : 2^180 % 1485 = 1 := by decide
private theorem period135 : 2^36 % 135 = 1 := by decide

private theorem r402_mod_odd (k : Nat) : 2^(402+4860*k) % 1485 = 334 := by
  have heq : 402+4860*k = 42+180*(2+27*k) := by omega
  rw [heq, pow_mod_period 1485 180 42 (2+27*k) (by omega) period1485]

private theorem r1738_mod_odd (k : Nat) : 2^(1738+4860*k) % 135 = 79 := by
  have heq : 1738+4860*k = 10+36*(48+135*k) := by omega
  rw [heq, pow_mod_period 135 36 10 (48+135*k) (by omega) period135]

private theorem even_pow (n : Nat) : (2^(n+1)) % 2 = 0 := by
  rw [Nat.pow_succ]
  omega

theorem r402_mod (k : Nat) : 2^(402+4860*k) % 2970 = 334 := by
  have hodd := r402_mod_odd k
  have he : 2^(402+4860*k)%2=0 := by
    rw [show 402+4860*k = (401+4860*k)+1 by omega]
    exact even_pow (401+4860*k)
  omega

theorem r1738_mod (k : Nat) : 2^(1738+4860*k) % 270 = 214 := by
  have hodd := r1738_mod_odd k
  have he : 2^(1738+4860*k)%2=0 := by
    rw [show 1738+4860*k = (1737+4860*k)+1 by omega]
    exact even_pow (1737+4860*k)
  omega

/-- This is definitionally identical to
`SheepEvenInverseAlgebra.GenericEdge` in the existing source-linked module. -/
def GenericEdge (x y : Nat) : Prop :=
  ∃ a h v u : Nat,
    1 ≤ a ∧ 5 ≤ v ∧ v % 2 = 1 ∧ u % 2 = 1 ∧
    x = 2^a * v ∧
    2*(1 + 2^h*u) + 1 = (2^(a+1)+1)*v + 2*a ∧
    y = 1 + 3^h*u

/-- All-k constructive incoming chain for the 402 congruence family. -/
theorem chain402 (k : Nat) :
    ∃ A B : Nat,
      GenericEdge A (2^(402+4860*k)) ∧ GenericEdge B A ∧
      15*A+2=8*2^(402+4860*k) ∧
      1485*B+4688=512*2^(402+4860*k) ∧
      10 < B ∧ B < A ∧ A < 2^(402+4860*k) := by
  let R := 2^(402+4860*k)
  have hmod : R % 2970 = 334 := r402_mod k
  let q := R / 2970
  have hR : R = 2970*q+334 := by
    have hh := Nat.mod_add_div R 2970
    omega
  let v1 := 792*q+89
  let v2 := 64*q+7
  let u1 := 990*q+111
  let u2 := 528*q+59
  let A := 2*v1
  let B := 16*v2
  have hroot : GenericEdge A R := by
    refine ⟨1,1,v1,u1,by omega,by dsimp [v1]; omega,?_,?_,?_,?_,?_⟩
    all_goals omega
  have hchild : GenericEdge B A := by
    refine ⟨4,1,v2,u2,by omega,by dsimp [v2]; omega,?_,?_,?_,?_,?_⟩
    all_goals omega
  refine ⟨A,B,hroot,hchild,?_,?_,?_,?_,?_⟩
  all_goals dsimp [A,B,v1,v2]; omega

/-- All-k constructive incoming chain for the 1738 congruence family. -/
theorem chain1738 (k : Nat) :
    ∃ A B : Nat,
      GenericEdge A (2^(1738+4860*k)) ∧ GenericEdge B A ∧
      15*A+2=8*2^(1738+4860*k) ∧
      135*B+196=64*2^(1738+4860*k) ∧
      10 < B ∧ B < A ∧ A < 2^(1738+4860*k) := by
  let R := 2^(1738+4860*k)
  have hmod : R % 270 = 214 := r1738_mod k
  let q := R / 270
  have hR : R = 270*q+214 := by
    have hh := Nat.mod_add_div R 270
    omega
  let v1 := 72*q+57
  let v2 := 32*q+25
  let u1 := 90*q+71
  let u2 := 144*q+113
  let A := 2*v1
  let B := 4*v2
  have hroot : GenericEdge A R := by
    refine ⟨1,1,v1,u1,by omega,by dsimp [v1]; omega,?_,?_,?_,?_,?_⟩
    all_goals omega
  have hchild : GenericEdge B A := by
    refine ⟨2,0,v2,u2,by omega,by dsimp [v2]; omega,?_,?_,?_,?_,?_⟩
    all_goals omega
  refine ⟨A,B,hroot,hchild,?_,?_,?_,?_,?_⟩
  all_goals dsimp [A,B,v1,v2]; omega

#print axioms chain402
#print axioms chain1738

end Audit
