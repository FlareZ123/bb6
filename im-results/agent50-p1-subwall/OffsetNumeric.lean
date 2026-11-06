import NumericPower148

namespace BB6.Agent50OffsetNumeric
open BB6.Agent43Numeric148

/-- A fixed factor 32 in the shell argument costs only five exponent bits.
    The large-shell induction has enough spare margin for it. -/
theorem poly_plus_five_below_pow (u : Nat) (hu : 9 ≤ u) :
    poly u+5 < 2^u := by
  have h : ∀ k : Nat, poly (k+9)+5 < 2^(k+9) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hlin : 4*(k+9)+17 ≤ poly (k+9) := by
        simp only [poly]
        omega
      have hinc := poly_increment (k+9)
      have hidx : (k+1)+9=(k+9)+1 := by omega
      rw [hidx, hinc, Nat.pow_succ]
      omega
  have heq : (u-9)+9=u := by omega
  simpa only [heq] using h (u-9)

/-- The dyadic-shell bound with an extra factor 3, for an arbitrary count z. -/
theorem shell_large_numeric_triple (n z : Nat)
    (hn : 512 ≤ n) (hz : 2^z ≤ 4*n) :
    3*24^z*(n+2)^(2*z+2) < 2^n := by
  obtain ⟨u,hu,hlo,hhi⟩ := shell_ge_9 n hn
  have hzu : z ≤ u+2 :=
    shell_parameter_bound n z u hu hlo hhi hz
  have hpow2 : 2^(u+2)=2*2^(u+1) := by
    have heq : u+2=(u+1)+1 := by omega
    rw [heq,Nat.pow_succ]
    omega
  have hpos : 1 ≤ 2^(u+1) := Nat.pow_pos (by decide)
  have hbase : n+2 ≤ 2^(u+2) := by
    rw [hpow2]
    omega
  have hbaseLeft : 24^z ≤ (2^5)^z :=
    Nat.pow_le_pow_left (by decide) z
  have hleft : 3*24^z ≤ (2^5)^(z+1) := by
    calc
      3*24^z ≤ 3*(2^5)^z := Nat.mul_le_mul_left 3 hbaseLeft
      _ ≤ (2^5)^z*32 := by
        have h := Nat.mul_le_mul_right ((2^5)^z) (show (3:Nat)≤32 by decide)
        simpa only [Nat.mul_comm] using h
      _ = (2^5)^(z+1) := by
        rw [Nat.pow_succ]
        simp only [show (2:Nat)^5=32 by decide]
  have hright : (n+2)^(2*z+2) ≤
      (2^(u+2))^(2*z+2) :=
    Nat.pow_le_pow_left hbase (2*z+2)
  have hprod : 3*24^z*(n+2)^(2*z+2) ≤
      (2^5)^(z+1)*(2^(u+2))^(2*z+2) :=
    Nat.mul_le_mul hleft hright
  have hpowRewrite :
      (2^5)^(z+1)*(2^(u+2))^(2*z+2) =
        2^(5*(z+1)+(u+2)*(2*z+2)) := by
    calc
      _ = 2^(5*(z+1))*2^((u+2)*(2*z+2)) := by
        rw [Nat.pow_mul, Nat.pow_mul]
      _ = 2^(5*(z+1)+(u+2)*(2*z+2)) :=
        (Nat.pow_add 2 (5*(z+1)) ((u+2)*(2*z+2))).symm
  have hpolyEq :
      5*(u+2)+(u+2)*(2*(u+2)+2) = poly u := by
    simp only [poly,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
    rw [Nat.mul_comm u (2*u)]
    omega
  have hmul : (u+2)*(2*z+2) ≤
      (u+2)*(2*(u+2)+2) :=
    Nat.mul_le_mul_left (u+2) (by omega)
  have hexp : 5*(z+1)+(u+2)*(2*z+2) ≤ poly u+5 := by omega
  have hle : 2^(5*(z+1)+(u+2)*(2*z+2)) ≤ 2^(poly u+5) :=
    Nat.pow_le_pow_right (by decide) hexp
  have hpolyStrict : 2^(poly u+5) < 2^(2^u) :=
    Nat.pow_lt_pow_right (by decide) (poly_plus_five_below_pow u hu)
  have hlast : 2^(2^u) ≤ 2^n :=
    Nat.pow_le_pow_right (by decide) hlo
  calc
    3*24^z*(n+2)^(2*z+2)
        ≤ (2^5)^(z+1)*(2^(u+2))^(2*z+2) := hprod
    _ = 2^(5*(z+1)+(u+2)*(2*z+2)) := hpowRewrite
    _ ≤ 2^(poly u+5) := hle
    _ < 2^(2^u) := hpolyStrict
    _ ≤ 2^n := hlast

#print axioms BB6.Agent50OffsetNumeric.poly_plus_five_below_pow
#print axioms BB6.Agent50OffsetNumeric.shell_large_numeric_triple

end BB6.Agent50OffsetNumeric
