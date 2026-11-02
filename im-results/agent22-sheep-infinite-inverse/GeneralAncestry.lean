import PeriodicAncestry

namespace BB6.Agent22.GeneralAncestry
open BB6.Agent22.InfiniteAncestry
open BB6.Agent22.PeriodicAncestry (W pow_one_mod W_ge_q)

/-- For any positive modulus, choose a power exponent in its zero residue class. -/
def exponentM (m n : Nat) : Nat := (2*3^(n+1))*m

def quotientM (m n : Nat) : Nat :=
  W (3^(n+2)) (Q (n+1)) m

theorem exponentM_divisible (m n : Nat) : m ∣ exponentM m n := by
  refine ⟨2*3^(n+1), ?_⟩
  unfold exponentM
  ac_rfl

theorem quotientM_ge_four (m n : Nat) (hm : 0<m) : 4 ≤ quotientM m n := by
  unfold quotientM
  have h := W_ge_q (3^(n+2)) (Q (n+1)) (m-1)
  have he : m-1+1=m := by omega
  rw [he] at h
  have hq := Q_step_ge_four n
  omega

theorem exponentM_congruence (m n : Nat) :
    2^(exponentM m n) = 1+3^(n+2)*quotientM m n := by
  have hbase := power_three_lifting (n+1)
  have hp := pow_one_mod (3^(n+2)) (Q (n+1)) m
  unfold exponentM quotientM
  rw [Nat.pow_mul, hbase]
  exact hp

def ancestorM (m n i : Nat) : Nat :=
  1 + 2^i * 3^((n+2)-i) * quotientM m n

theorem ancestorM_zero (m n : Nat) :
    ancestorM m n 0 = 2^(exponentM m n) := by
  have hp := exponentM_congruence m n
  unfold ancestorM
  have he : n+2-0=n+2 := by omega
  rw [he]
  simp only [Nat.pow_zero, Nat.one_mul]
  exact hp.symm

private theorem ancestorM_step_relation (m n i : Nat) (hi : i+1 ≤ n+2) :
    2*(ancestorM m n i) + 1 = 3*(ancestorM m n (i+1)) := by
  have he : (n+2)-i = ((n+2)-(i+1))+1 := by omega
  have hp3 : 3^((n+2)-i) = 3^((n+2)-(i+1))*3 := by
    rw [he,Nat.pow_succ]
  have hp2 : 2^(i+1) = 2^i*2 := by rw [Nat.pow_succ]
  unfold ancestorM
  rw [hp3,hp2]
  simp only [Nat.mul_add, Nat.add_mul]
  have hmul :
      2*((2^i*(3^((n+2)-(i+1))*3))*quotientM m n) =
        3*((2^i*2*3^((n+2)-(i+1)))*quotientM m n) := by ac_rfl
  omega

private theorem ancestorM_generic (m n i : Nat) (hm : 0<m) :
    5 ≤ ancestorM m n (i+1) ∧ (ancestorM m n (i+1))%2=1 := by
  let v := 2^i * 3^((n+2)-(i+1)) * quotientM m n
  have hx : ancestorM m n (i+1)=1+2*v := by
    unfold ancestorM v
    rw [Nat.pow_succ]
    ac_rfl
  have hq : 4 ≤ quotientM m n := quotientM_ge_four m n hm
  have hpos : 0<2^i * 3^((n+2)-(i+1)) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hbig : quotientM m n ≤ v := by
    exact Nat.le_mul_of_pos_left _ hpos
  rw [hx]
  constructor <;> omega

/-- Every step along the constructed chain is a genuine Sheep generic edge. -/
theorem ancestorM_predecessor (m n i : Nat) (hm : 0<m) (hi : i+1 ≤ n+2) :
    SheepBridge.SectionNext (ancestorM m n (i+1)) (ancestorM m n i) := by
  obtain ⟨hge,hodd⟩ := ancestorM_generic m n i hm
  have heq := ancestorM_step_relation m n i hi
  have htarget : ancestorM m n (i+1)+(ancestorM m n (i+1)-1)/2 =
      ancestorM m n i := by omega
  have hnext := SheepBridge.SectionNext.general 0 (ancestorM m n (i+1)) hge hodd
  simpa [htarget] using hnext

theorem finite_ancestryM (m n i : Nat) (hm : 0<m) (hi : i≤n+1) :
    SectionChain i (ancestorM m n i) (ancestorM m n 0) := by
  induction i with
  | zero => exact SectionChain.refl _
  | succ i ih =>
    exact SectionChain.cons (ancestorM_predecessor m n i hm (by omega)) (ih (by omega))

/-- For every finite inverse depth and every modulus, including arbitrarily
large moduli, a halting power with exponent congruent zero modulo the modulus
admits a genuine generic inverse chain of the prescribed length. -/
theorem every_modulus_has_unbounded_inverse_chains (m : Nat) (hm : 0<m) (n : Nat) :
    ∃ j t : Nat, m ∣ j ∧ SectionChain n t (2^j) := by
  refine ⟨exponentM m n, ancestorM m n n, exponentM_divisible m n, ?_⟩
  rw [←ancestorM_zero m n]
  exact finite_ancestryM m n n hm (by omega)

#print axioms BB6.Agent22.GeneralAncestry.every_modulus_has_unbounded_inverse_chains

/-- There are infinitely many distinct halting-power exponents in the
zero residue class of every modulus with genuine generic ancestors
at least any prescribed finite depth. -/
theorem arbitrarily_large_exponents_have_deep_chains
    (m : Nat) (hm : 0<m) (n K : Nat) :
    ∃ j t : Nat, K < j ∧ m ∣ j ∧ SectionChain n t (2^j) := by
  let modulus := m*(K+1)
  have hmod : 0<modulus := Nat.mul_pos hm (by omega)
  let j := exponentM modulus n
  let t := ancestorM modulus n n
  have h1 : K+1 ≤ modulus := by
    exact Nat.le_mul_of_pos_left _ hm
  have hfact : 0 < 2*3^(n+1) :=
    Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have h2 : modulus ≤ j := by
    dsimp [j, exponentM]
    exact Nat.le_mul_of_pos_left _ hfact
  have hmdiv : m ∣ j := by
    refine ⟨(2*3^(n+1))*(K+1),?_⟩
    dsimp [j,exponentM,modulus]
    ac_rfl
  refine ⟨j,t,by omega,hmdiv,?_⟩
  dsimp [j,t]
  rw [←ancestorM_zero modulus n]
  exact finite_ancestryM modulus n n hmod (by omega)

#print axioms BB6.Agent22.GeneralAncestry.arbitrarily_large_exponents_have_deep_chains

end BB6.Agent22.GeneralAncestry
