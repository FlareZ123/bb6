import Std
namespace BB6.Agent8Zero

theorem n_plus_four_le_pow (n : Nat) (hn : 4 ≤ n) : n+4 ≤ 2^n := by
  have hall : ∀ i : Nat, i+4+4 ≤ 2^(i+4) := by
    intro i
    induction i with
    | zero => decide
    | succ i ih =>
        have hidx : (i+1)+4=(i+4)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have hidx : (n-4)+4=n := by omega
  simpa only [hidx] using hall (n-4)

/-- Critical inverse cost must be large if the exact even power and
bounded final inverse depth are simultaneously satisfied at c=0. -/
theorem zero_even_mass_forces_large_cost
    (n P Q m t : Nat)
    (hpow : n+4 ≤ P)
    (ht : t ≤ n+2)
    (hQ : 2*Q ≤ P)
    (hmass : 7*Q + n+m+t+3 = 7*P) :
    3*P+6 ≤ 2*m := by
  omega

/-- Exact critical mass, inverse power and reachable even-left coordinate
equations force exponential cumulative inverse cost at an output c=0. -/
theorem c_zero_critical_math
    (n b d m t k j : Nat)
    (hnP : n+4 ≤ 2^n)
    (hroot : b+d+2*m+2*n+13=14*2^n)
    (hpow : d+b/2+3=3*2^t)
    (hinv : 2*k+2*t+1=b+d)
    (hreach : 2*k+8=14*2^j) :
    3*2^n+6 ≤ 2*m := by
  let P : Nat := 2^n
  have hEq : 7*2^j+n+m+t+3=7*P := by dsimp [P]; omega
  have hjn : j<n := by
    by_cases hj : j<n
    · exact hj
    · have hge : n≤j := by omega
      have hmono : (2:Nat)^n ≤ 2^j := Nat.pow_le_pow_right (by decide) hge
      dsimp [P] at hEq
      omega
  have hjle : j+1≤n := by omega
  have hmono : (2:Nat)^(j+1)≤2^n := Nat.pow_le_pow_right (by decide) hjle
  have hjpow : (2:Nat)^(j+1)=2*2^j := by
    rw [Nat.pow_succ]
    omega
  have hQ : 2*2^j ≤ P := by dsimp [P]; omega
  have hbdiv : b/2≤b := Nat.div_le_self b 2
  have htop : 3*2^t≤14*P+3 := by dsimp [P]; omega
  have ht : t≤n+2 := by
    by_cases htt : t≤n+2
    · exact htt
    · have hge : n+3≤t := by omega
      have hmono : (2:Nat)^(n+3)≤2^t := Nat.pow_le_pow_right (by decide) hge
      have hEight : (2:Nat)^(n+3)=8*P := by
        dsimp [P]
        rw [Nat.pow_add]
        have h8 : (2:Nat)^3=8 := by decide
        rw [h8]
        omega
      have hmul := Nat.mul_le_mul_left 3 hmono
      have hPpos : 0 < P := Nat.pow_pos (by decide)
      omega
  have hmass := zero_even_mass_forces_large_cost n P (2^j) m t
    (by simpa only [P] using hnP) ht hQ hEq
  simpa only [P] using hmass

#print axioms BB6.Agent8Zero.c_zero_critical_math
end BB6.Agent8Zero
