import PowerCorridor

namespace BB6.Agent39Sheep
open BB6.Agent39Three (W pow_one_mod)

/-- Parametric modulus and residue witness. Given a period 3^e ≡ 1 (mod m),
    every residue d*s modulo d*m, d=2*3^b, admits arbitrary-depth genuine
    generic valuation-zero Sheep inverse ancestry. -/
theorem generic_periodic_residue_depth
    (b m e q s k : Nat) (he : 0<e) (hperiod : 3^e=1+m*q)
    (hs : 0<s) :
    ∃ j x, j % ((2*3^b)*m) = ((2*3^b)*s) % ((2*3^b)*m) ∧
      Chain0 (k+1) x (2^j) := by
  let d : Nat := 2*3^b
  let j : Nat := (d*s)*3^(e*(k+1))
  have hp : 3^(e*(k+1)) = 1+m*W m q (k+1) := by
    rw [Nat.pow_mul,hperiod]
    exact pow_one_mod m q (k+1)
  have hjmod : j % (d*m)=(d*s)%(d*m) := by
    dsimp [j]
    rw [hp]
    have heq : (d*s)*(1+m*W m q (k+1)) =
        d*s+(d*m)*(s*W m q (k+1)) := by
      simp only [Nat.mul_add, Nat.mul_one]
      ac_rfl
    rw [heq]
    simp [Nat.add_mod, Nat.mul_mod]
  have hlen : k ≤ e*(k+1) := by
    have hh : k+1 ≤ e*(k+1) := Nat.le_mul_of_pos_left _ he
    omega
  have hdiff : e*(k+1)=k+(e*(k+1)-k) := by omega
  have hjdiv : 2*3^k ∣ j := by
    refine ⟨3^b*s*3^(e*(k+1)-k), ?_⟩
    dsimp [j,d]
    have hpowfactor : 3^(e*(k+1)) = 3^k*3^(e*(k+1)-k) := by
      calc
        3^(e*(k+1)) = 3^(k+(e*(k+1)-k)) :=
          congrArg (fun z : Nat => 3^z) hdiff
        _ = 3^k*3^(e*(k+1)-k) := by rw [Nat.pow_add]
    rw [hpowfactor]
    ac_rfl
  have hjlarge : 3 ≤ j := by
    have hexp : 0<e*(k+1) := Nat.mul_pos he (by omega)
    have hp3 : (3:Nat)^1 ≤ 3^(e*(k+1)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hcoeff : 0 < d*s := by
      exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hs
    have hm : 3^(e*(k+1)) ≤ (d*s)*3^(e*(k+1)) :=
      Nat.le_mul_of_pos_left _ hcoeff
    dsimp [j]
    omega
  obtain ⟨x,hchain⟩ := (power_corridor_iff k j hjlarge).mpr hjdiv
  exact ⟨j,x,hjmod,hchain⟩

#print axioms generic_periodic_residue_depth
end BB6.Agent39Sheep
