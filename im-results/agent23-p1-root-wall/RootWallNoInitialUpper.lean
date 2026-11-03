import Std

namespace BB6.Agent23RootWall

/-- A quantitative polynomial-versus-exponential bound, useful for every
    critical index n >= 14. -/
private theorem quad_power (n:Nat) (hn:14≤n) : 32*n*n ≤ 2^n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h : ∀ k : Nat, 32*(14+k)*(14+k) ≤ 2^(14+k) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      let N := 14+k
      have hN : 3 ≤ N := by dsimp [N]; omega
      have hmul : 3*N ≤ N*N := Nat.mul_le_mul_right N hN
      have hquad : (N+1)*(N+1) = N*N + 2*N + 1 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      have hnew : N*N + 2*N + 1 ≤ 2*(N*N) := by omega
      have hrewrite : 32*(N+1)*(N+1) ≤ 2*(32*N*N) := by
        calc
          32*(N+1)*(N+1) = 32*((N+1)*(N+1)) := by simp [Nat.mul_assoc]
          _ = 32*(N*N+2*N+1) := by rw [hquad]
          _ ≤ 32*(2*(N*N)) := Nat.mul_le_mul_left 32 hnew
          _ = 2*(32*N*N) := by simp [Nat.mul_assoc, Nat.mul_comm]
      have hp : 2^(14+(k+1)) = 2*(2^(14+k)) := by
        rw [show 14+(k+1)=(14+k)+1 by omega, Nat.pow_succ]
        omega
      rw [hp]
      change 32*(N+1)*(N+1) ≤ 2*2^(14+k)
      have hih : 32*N*N ≤ 2^(14+k) := ih
      have hscaled := Nat.mul_le_mul_left 2 hih
      omega
  simpa using h k

/-- The true P1 critical root can never enter its exponential-cost affine
    wall by any number of pure depth-zero inverses, for any index n >= 14. -/
theorem no_root_upper_wall (n L:Nat) (hn:14≤n) :
    14*2^n ≠ 2^L*(4*(n+L)+12) + 2*n+4 := by
  intro heq
  have hL : L<n := by
    by_cases hl:n≤L
    · have hp:2^n≤2^L:=Nat.pow_le_pow_right (by decide) hl
      have hc:14≤4*(n+L)+12:=by omega
      have hprod:14*2^n≤2^L*(4*(n+L)+12):=by
        calc
          14*2^n ≤ 14*2^L := Nat.mul_le_mul_left 14 hp
          _ ≤ (4*(n+L)+12)*2^L := Nat.mul_le_mul_right (2^L) hc
          _ = 2^L*(4*(n+L)+12) := by ac_rfl
      omega
    · omega
  have hdiv : 2^L ∣ (2*n+4) := by
    have hp:2^L ∣ 14*2^n:=by
      obtain ⟨x,hx⟩:=Nat.pow_dvd_pow 2 (show L≤n by omega)
      refine ⟨14*x, ?_⟩
      rw [hx]
      ac_rfl
    have hp2:2^L ∣ 2^L*(4*(n+L)+12):=⟨4*(n+L)+12,rfl⟩
    have hs:2^L∣2^L*(4*(n+L)+12)+(2*n+4):=by
      have hrewrite:2^L*(4*(n+L)+12)+(2*n+4)=14*2^n := by omega
      rw [hrewrite]
      exact hp
    exact (Nat.dvd_add_iff_right hp2).mpr hs
  have hpowle:2^L≤2*n+4:=Nat.le_of_dvd (by omega) hdiv
  have hcoeff:4*(n+L)+12≤8*n+12:=by omega
  have hprod:2^L*(4*(n+L)+12)≤(2*n+4)*(8*n+12) :=
    Nat.mul_le_mul hpowle hcoeff
  have hp32:=quad_power n hn
  have hmult : 14*n≤n*n := Nat.mul_le_mul_right n hn
  have hid : (2*n+4)*(8*n+12)+2*n+4 = 16*(n*n)+58*n+52 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have hpolylow : 16*(n*n)+58*n+52<32*(n*n) := by omega
  have hp32' :32*(n*n) ≤ 2^n := by simpa [Nat.mul_assoc] using hp32
  have hgap : (2*n+4)*(8*n+12)+2*n+4<2^n:=by rw [hid]; omega
  omega

#print axioms no_root_upper_wall
end BB6.Agent23RootWall
