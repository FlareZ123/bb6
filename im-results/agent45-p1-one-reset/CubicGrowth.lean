import Std
namespace BB6.Agent45OneReset

/-- For every n≥30, the dyadic scale dominates the cubic correction
    required by the complete one-positive-reset inverse obstruction. -/
theorem cubic_growth_all (n:Nat) (hn:30≤n) : 512*n*n*n ≤ 2^n := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h : ∀ w:Nat, 512*(30+w)*(30+w)*(30+w)≤2^(30+w) := by
    intro w
    induction w with
    | zero => decide
    | succ w ih =>
      let N:=30+w
      have hnN : 30≤N := by dsimp [N]; omega
      have hNpos : 1≤N := by omega
      have hNN : N≤N*N := by
        have hh:=Nat.mul_le_mul_left N hNpos
        omega
      have hNNpos : 1≤N*N := by omega
      have h7 : 7*(N*N)≤N*N*N := by
        have hh:=Nat.mul_le_mul_right (N*N) (show 7≤N by omega)
        simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
      have hmid : 3*(N*N)+3*N+1≤N*N*N := by omega
      have hcube : (N+1)*(N+1)*(N+1) ≤ 2*(N*N*N) := by
        have hform : (N+1)*(N+1)*(N+1)=N*N*N+3*(N*N)+3*N+1 := by
          simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          omega
        omega
      have hscaled := Nat.mul_le_mul_left 512 hcube
      have hd : 512*(N+1)*(N+1)*(N+1)≤2*(512*N*N*N) := by
        calc
          _ ≤ 512*(2*(N*N*N)) := by simpa [Nat.mul_assoc] using hscaled
          _ = 2*(512*N*N*N) := by ac_rfl
      have hpow : 2^(N+1)=2*2^N := by rw [Nat.pow_succ]; omega
      have hprev : 512*N*N*N≤2^N := by simpa [N] using ih
      have hh2 := Nat.mul_le_mul_left 2 hprev
      have hres : 512*(N+1)*(N+1)*(N+1) ≤ 2^(N+1) := by
        rw [hpow]
        exact Nat.le_trans hd hh2
      simpa only [show 30+(w+1)=N+1 by dsimp [N]; omega] using hres
  simpa only [Nat.add_assoc] using h w

#print axioms cubic_growth_all
end BB6.Agent45OneReset
