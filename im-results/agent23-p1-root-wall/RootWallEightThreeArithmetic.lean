import CriticalRootWallArithmetic

namespace BB6.Agent23RootWall

private theorem growth_eight (n:Nat) (hn:4≤n) :
    14*n+34 < 8*2^n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have aux : ∀ r : Nat, 14*(4+r)+34 < 8*2^(4+r) := by
    intro r
    induction r with
    | zero => decide
    | succ r ih =>
      have hpow : 2^(4+(r+1)) = 2*(2^(4+r)) := by
        rw [show 4+(r+1)=(4+r)+1 by omega, Nat.pow_succ]
        omega
      rw [hpow]
      omega
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using aux r

theorem no_low_wall_eight_three_power (n m u z:Nat)
    (hn:4≤n) (hm:m<2^n)
    (hbalance:8*u+4*n+2*m+22=14*2^n)
    (hpower:6*u+8=14*2^z) : False := by
  have hg:=growth_eight n hn
  have hhalf : 2^n=2*2^(n-1) := by
    have hnval : n=(n-1)+1 := by omega
    calc
      2^n = 2^((n-1)+1) := by congr 1
      _ = 2*2^(n-1) := by rw [Nat.pow_succ]; omega
  have hlo : 7*2^n < 6*u+8 := by omega
  have hhi : 6*u+8 < 14*2^n := by omega
  by_cases hzlt : z<n
  · have hzle:z≤n-1:=by omega
    have hp:2^z≤2^(n-1):=Nat.pow_le_pow_right (by decide) hzle
    omega
  · have hge:n≤z:=by omega
    have hp:2^n≤2^z:=Nat.pow_le_pow_right (by decide) hge
    omega

#print axioms no_low_wall_eight_three_power
end BB6.Agent23RootWall
