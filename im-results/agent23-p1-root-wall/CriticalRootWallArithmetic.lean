import Std

namespace BB6.Agent23RootWall

theorem exp_growth (n : Nat) (hn : 4 ≤ n) :
    14*n+10 < 8*2^n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have aux : ∀ r : Nat, 14*(4+r)+10 < 8*2^(4+r) := by
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

/-- Arithmetic dichotomy for every P1 critical root; the source-connected
    blank-orbit theorem is in CriticalRootWallOriginal. -/
theorem critical_root_even_exit_wall_or_exponential
    (n b d m t k c j : Nat) (hn : 4 ≤ n)
    (hroot : b+d+2*m+2*n+13 = 14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3 = 2^t*(c+3))
    (heven : c%2=0) (hc : 2≤c)
    (hlinear : 2*k+c+2*t+1=b+d)
    (hevenpower : 2*k+8=14*2^j) :
    2^n ≤ m ∨ (t=1 ∧ j+1=n ∧ b=4*(n+m)) := by
  let P := 2^n
  have hP : P = 2^n := rfl
  have hPpos : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by decide)
  have hgrowth : 14*n+10 < 8*P := by simpa [P] using exp_growth n hn
  have hdiv : b/2 ≤ b := Nat.div_le_self b 2
  have hdodd : d%2=1 := by omega
  have hbeven : (b/2)%2=0 := by omega
  have htpos : 1≤t := by
    by_cases htzero : t=0
    · have he : 2^t=1 := by rw [htzero]
      rw [he] at hpower
      omega
    · omega
  have htpow : t≤n+1 := by
    by_cases hnot : t≤n+1
    · exact hnot
    have hge : n+2≤t := by omega
    have hpowle : 2^(n+2)≤2^t := Nat.pow_le_pow_right (by omega) hge
    have hpowid : 2^(n+2)=4*P := by
      rw [Nat.pow_add]
      simp [P, Nat.mul_comm]
    have hcap : 2^t*(c+3) ≤ b+d+3 := by
      rw [←hpower]
      omega
    rw [hpowid] at hpowle
    have : 4*P*5 ≤ 2^t*(c+3) := Nat.mul_le_mul hpowle (by omega : 5≤c+3)
    omega
  have hjbound : j+1≤n := by
    by_cases hnot : j+1≤n
    · exact hnot
    have hge : n≤j := by omega
    have hpowle : 2^n≤2^j := Nat.pow_le_pow_right (by omega) hge
    omega
  have hqbound : 2*2^j ≤ P := by
    have hh : 2^(j+1)≤2^n := Nat.pow_le_pow_right (by omega) hjbound
    rw [Nat.pow_succ] at hh
    omega
  by_cases hlarge : P≤m
  · exact Or.inl hlarge
  right
  have hsmall : m<P := by omega
  have ht : t=1 := by
    by_cases htone : t=1
    · exact htone
    have httwo : 2≤t := by omega
    have hfour : 4≤2^t := by
      have hh : 2^2≤2^t := Nat.pow_le_pow_right (by omega) httwo
      have he : (2:Nat)^2=4 := by decide
      rwa [he] at hh
    have hcap : 4*(c+3) ≤ b+d+3 := by
      have hp : 4*(c+3) ≤ 2^t*(c+3) := Nat.mul_le_mul_right (c+3) hfour
      rw [←hpower] at hp
      omega
    have hpowub : 2*k+8 ≤ 7*P := by omega
    omega
  have hj : j+1=n := by
    by_cases hjeq : j+1=n
    · exact hjeq
    have hjtwo : j+2≤n := by omega
    have hpowquarter : 4*2^j≤P := by
      have hp : 2^(j+2)≤2^n := Nat.pow_le_pow_right (by omega) hjtwo
      rw [Nat.pow_add] at hp
      have he : (2:Nat)^2=4 := by decide
      rw [he] at hp
      omega
    have hcap : 2*(c+3)≤b+d+3 := by
      have htwo : 2^t=2 := by simp [ht]
      rw [htwo] at hpower
      omega
    omega
  have hpowhalf : P=2*2^j := by
    have hnj : n=j+1 := by omega
    rw [hnj, Nat.pow_succ] at hP
    omega
  have hcap : 2*(c+3)=d+b/2+3 := by simpa [ht] using hpower.symm
  constructor
  · exact ht
  constructor
  · exact hj
  · omega

#print axioms critical_root_even_exit_wall_or_exponential
end BB6.Agent23RootWall
