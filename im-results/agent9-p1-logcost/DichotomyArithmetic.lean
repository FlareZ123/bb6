import Init.Omega
namespace BB6.Agent9Dichotomy

/-- An even feeder with a depth >=2 G inverse and a reachable power shape
    requires an exponential prior inverse cost. -/
theorem deep_even_exit_large_cost
    (q u e b d m t k c j : Nat)
    (hq : 1 ≤ q)
    (he : e = 3 ∨ e = 5)
    (hu : u + 4*q + 3 = 7*2^(16*q))
    (hmass : b+d+2*m = 8*u+e)
    (hdiv : b%4=0)
    (hinverse : d+b/2+3=2^t*(c+3))
    (hcost : 2*k+c+2*t+1 = b+d)
    (hpower : 2*k+8 = 14*2^j)
    (hj : j≤16*q+1)
    (htbound : t≤16*q+4)
    (hP : 256*q ≤ 2^(16*q))
    (ht : 2≤t) :
    8*2^(16*q) ≤ m := by
  have ht4 : 4 ≤ 2^t := by
    have hh : 2^2 ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) ht
    simpa using hh
  have hc4 : 4*(c+3) ≤ d+b/2+3 := by
    calc
      4*(c+3) ≤ 2^t*(c+3) := Nat.mul_le_mul_right (c+3) ht4
      _ = d+b/2+3 := hinverse.symm
  have hjpow : 2^j ≤2^(16*q+1) :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj
  have htop : 14*2^j ≤ 28*2^(16*q) := by
    have hw : 2^(16*q+1) = 2*2^(16*q) := by rw [Nat.pow_succ]; omega
    omega
  have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
  rcases he with he | he <;> omega

/-- A depth-one inverse lies on a unique wall unless its path is very deep. -/
theorem depth_one_even_exit_wall_or_large
    (q u e b d m k c j : Nat)
    (hq : 1 ≤ q)
    (he : e = 3 ∨ e = 5)
    (hu : u + 4*q + 3 = 7*2^(16*q))
    (hmass : b+d+2*m=8*u+e)
    (hb4 : b%4=0)
    (hinverse : d+b/2+3=2*(c+3))
    (hcost : 2*k+c+3=b+d)
    (hpower : 2*k+8=14*2^j)
    (hj : j≤16*q+1)
    (hP : 256*q ≤2^(16*q)) :
    8*2^(16*q) ≤ m ∨
      ((e=3 ∧ b=4*m+64*q+16) ∨ (e=5 ∧ b=4*m+64*q+12)) := by
  by_cases hnext : j=16*q+1
  · right
    have hjpow:2^j=2*2^(16*q) := by
      rw [hnext,Nat.pow_succ]
      omega
    have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
    rcases he with he | he <;> omega
  · left
    have hjle:j≤16*q := by omega
    have hjpow : 2^j≤2^(16*q) :=
      Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hjle
    have htop : 14*2^j ≤ 14*2^(16*q) := by omega
    have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
    rcases he with he | he <;> omega

theorem terminal_power_index_bound
    (q u e b d m t k c j : Nat)
    (he : e = 3 ∨ e = 5)
    (hu : u + 4*q + 3 = 7*2^(16*q))
    (hmass : b+d+2*m=8*u+e)
    (hcost : 2*k+c+2*t+1=b+d)
    (hpower : 2*k+8=14*2^j) :
    j ≤ 16*q+1 := by
  have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
  have hupper : 14*2^j < 56*2^(16*q) := by
    rcases he with he | he <;> omega
  by_cases hj : j ≤16*q+1
  · exact hj
  · have hge : 16*q+2 ≤ j := by omega
    have hp : 2^(16*q+2) ≤ 2^j :=
      Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hge
    have hs : 2^(16*q+2) = 4*2^(16*q) := by
      rw [Nat.pow_add]
      omega
    omega

/-- Every power-shaped exit meets the exponential-cost bound or the
    source's single feasible depth-one affine wall. -/
theorem even_terminal_exponential_or_wall
    (q u e b d m t k c j : Nat)
    (hq : 1 ≤ q)
    (he : e=3 ∨ e=5)
    (hu : u+4*q+3=7*2^(16*q))
    (hmass : b+d+2*m=8*u+e)
    (hb4 : b%4=0)
    (hdodd : d%2=1)
    (hceven : c%2=0)
    (hinverse : d+b/2+3=2^t*(c+3))
    (hcost : 2*k+c+2*t+1=b+d)
    (hpower : 2*k+8=14*2^j)
    (htbound : t≤16*q+4)
    (hP : 256*q≤2^(16*q)) :
    8*2^(16*q) ≤ m ∨
      (t=1 ∧ ((e=3 ∧ b=4*m+64*q+16) ∨
        (e=5 ∧ b=4*m+64*q+12))) := by
  have hj := terminal_power_index_bound q u e b d m t k c j he hu hmass hcost hpower
  have hnot0 : t ≠ 0 := by
    intro ht
    subst t
    simp only [Nat.pow_zero, Nat.one_mul] at hinverse
    omega
  by_cases htdeep : 2≤t
  · left
    exact deep_even_exit_large_cost q u e b d m t k c j hq he hu
      hmass hb4 hinverse hcost hpower hj htbound hP htdeep
  · have htone : t=1 := by omega
    have hinverse1 : d+b/2+3=2*(c+3) := by
      simpa [htone] using hinverse
    have hcost1 : 2*k+c+3=b+d := by omega
    rcases depth_one_even_exit_wall_or_large q u e b d m k c j
      hq he hu hmass hb4 hinverse1 hcost1 hpower hj hP with hlarge | hwall
    · exact Or.inl hlarge
    · exact Or.inr ⟨htone,hwall⟩

#print axioms terminal_power_index_bound
#print axioms even_terminal_exponential_or_wall
#print axioms deep_even_exit_large_cost
#print axioms depth_one_even_exit_wall_or_large
end BB6.Agent9Dichotomy
