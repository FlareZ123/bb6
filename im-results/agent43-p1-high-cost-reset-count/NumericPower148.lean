import NumericShell

namespace BB6.Agent43Numeric148

/-- With 2^z<=4n, the logarithmic shell index controls z. -/
theorem shell_parameter_bound (n z u : Nat)
    (hu : 9 ≤ u) (hlo : 2^u ≤ n)
    (hhi : n < 2^(u+1)) (hz : 2^z ≤ 4*n) :
    z ≤ u+2 := by
  have hpow4 : 2^(u+3)=4*2^(u+1) := by
    have heq : u+3=(u+1)+2 := by omega
    rw [heq, Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega
  have hmax : 4*n < 2^(u+3) := by
    rw [hpow4]
    omega
  by_cases hzu : z ≤ u+2
  · exact hzu
  · have hlow : u+3 ≤ z := by omega
    have hp := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hlow
    omega

/-- The entire infinite high dyadic tail n>=512 is covered by one
    polynomial/exponential induction in the shell index u>=9. -/
theorem shell_large_numeric (n z : Nat)
    (hn : 512 ≤ n) (hz : 2^z ≤ 4*n) :
    24^z*(n+2)^(2*z+2) < 2^n := by
  obtain ⟨u,hu,hlo,hhi⟩ := shell_ge_9 n hn
  have hzu : z ≤ u+2 :=
    shell_parameter_bound n z u hu hlo hhi hz
  have hpow2 : 2^(u+2)=2*2^(u+1) := by
    have heq : u+2=(u+1)+1 := by omega
    rw [heq,Nat.pow_succ]
    omega
  have hpos : 1 ≤ 2^(u+1) := by
    exact Nat.pow_pos (by decide)
  have hbase : n+2 ≤ 2^(u+2) := by
    rw [hpow2]
    omega
  have hleft : 24^z ≤ (2^5)^z :=
    Nat.pow_le_pow_left (by decide) z
  have hright : (n+2)^(2*z+2) ≤
      (2^(u+2))^(2*z+2) :=
    Nat.pow_le_pow_left hbase (2*z+2)
  have hprod : 24^z*(n+2)^(2*z+2) ≤
      (2^5)^z*(2^(u+2))^(2*z+2) :=
    Nat.mul_le_mul hleft hright
  have hpowRewrite :
      (2^5)^z*(2^(u+2))^(2*z+2) =
        2^(5*z+(u+2)*(2*z+2)) := by
    calc
      (2^5)^z*(2^(u+2))^(2*z+2) =
          2^(5*z)*2^((u+2)*(2*z+2)) := by
            rw [Nat.pow_mul, Nat.pow_mul]
      _ = 2^(5*z+(u+2)*(2*z+2)) :=
        (Nat.pow_add 2 (5*z) ((u+2)*(2*z+2))).symm
  have hpolyEq :
      5*(u+2)+(u+2)*(2*(u+2)+2) = poly u := by
    simp only [poly,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
    rw [Nat.mul_comm u (2*u)]
    omega
  have hmul : (u+2)*(2*z+2) ≤
      (u+2)*(2*(u+2)+2) :=
    Nat.mul_le_mul_left (u+2) (by omega)
  have hexp : 5*z+(u+2)*(2*z+2) ≤ poly u := by omega
  have hle : 2^(5*z+(u+2)*(2*z+2)) ≤ 2^(poly u) :=
    Nat.pow_le_pow_right (by decide) hexp
  have hpolyStrict : 2^(poly u) < 2^(2^u) :=
    Nat.pow_lt_pow_right (by decide) (poly_below_pow u hu)
  have hlast : 2^(2^u) ≤ 2^n :=
    Nat.pow_le_pow_right (by decide) hlo
  calc
    24^z*(n+2)^(2*z+2)
        ≤ (2^5)^z*(2^(u+2))^(2*z+2) := hprod
    _ = 2^(5*z+(u+2)*(2*z+2)) := hpowRewrite
    _ ≤ 2^(poly u) := hle
    _ < 2^(2^u) := hpolyStrict
    _ ≤ 2^n := hlast

#print axioms BB6.Agent43Numeric148.shell_parameter_bound
#print axioms BB6.Agent43Numeric148.shell_large_numeric

end BB6.Agent43Numeric148
