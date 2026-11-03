import CriticalRootWallArithmetic

namespace BB6.Agent23RootWall

/-- For every n>=4, any non-wall critical-root even feeder must have
    inverse cost m with 14*2^n <= 6*m+14*n+10. -/
theorem critical_root_even_exit_sharp_budget
    (n b d m t k c j : Nat) (hn : 4 ≤ n)
    (hroot : b+d+2*m+2*n+13 = 14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3 = 2^t*(c+3))
    (heven : c%2=0) (hc : 2≤c)
    (hlinear : 2*k+c+2*t+1=b+d)
    (hevenpower : 2*k+8=14*2^j) :
    14*2^n ≤ 6*m+14*n+10 ∨
    (t=1 ∧ j+1=n ∧ b=4*(n+m)) := by
  let P := 2^n
  have hP : P=2^n := rfl
  have hPpos : 0<P := by dsimp [P]; exact Nat.pow_pos (by decide)
  have hdiv : b/2≤b := Nat.div_le_self b 2
  have hdodd : d%2=1 := by omega
  have hbeven : (b/2)%2=0 := by omega
  have htpos : 1≤t := by
    by_cases hzero:t=0
    · have hp : 2^t=1 := by rw [hzero]
      rw [hp] at hpower
      omega
    · omega
  have htbound : t≤n+1 := by
    by_cases hgood : t≤n+1
    · exact hgood
    have hge:n+2≤t:=by omega
    have hp : 2^(n+2)≤2^t := Nat.pow_le_pow_right (by omega) hge
    have hid : 2^(n+2)=4*P := by rw [Nat.pow_add]; simp [P,Nat.mul_comm]
    have hcap : 2^t*(c+3)≤b+d+3 := by rw [←hpower]; omega
    rw [hid] at hp
    have hh : 4*P*5≤2^t*(c+3) := Nat.mul_le_mul hp (by omega:5≤c+3)
    omega
  have hjbound:j+1≤n := by
    by_cases hgood:j+1≤n
    · exact hgood
    have hge:n≤j:=by omega
    have hp:2^n≤2^j:=Nat.pow_le_pow_right (by omega) hge
    omega
  have hqbound : 2*2^j≤P := by
    have hp:2^(j+1)≤2^n:=Nat.pow_le_pow_right (by omega) hjbound
    rw [Nat.pow_succ] at hp
    omega
  by_cases ht:t=1
  · by_cases hj:j+1=n
    · right
      have hhalf:P=2*2^j := by
        have hnj:n=j+1:=by omega
        rw [hnj,Nat.pow_succ] at hP
        omega
      have hcap:2*(c+3)=d+b/2+3:=by simpa [ht] using hpower.symm
      exact ⟨ht,hj,by omega⟩
    · left
      have hjtwo:j+2≤n:=by omega
      have hquarter:4*2^j≤P := by
        have hp:2^(j+2)≤2^n:=Nat.pow_le_pow_right (by omega) hjtwo
        rw [Nat.pow_add] at hp
        have he:(2:Nat)^2=4:=by decide
        rw [he] at hp
        omega
      have hcap:2*(c+3)≤b+d+3 := by
        have hp:2^t=2:=by simp [ht]
        rw [hp] at hpower
        omega
      omega
  · left
    have httwo:2≤t:=by omega
    have hfour:4≤2^t := by
      have hp:2^2≤2^t:=Nat.pow_le_pow_right (by omega) httwo
      have he:(2:Nat)^2=4:=by decide
      rwa [he] at hp
    have hcap:4*(c+3)≤b+d+3 := by
      have hp:4*(c+3)≤2^t*(c+3):=Nat.mul_le_mul_right (c+3) hfour
      rw [←hpower] at hp
      omega
    have hq:2*k+8≤7*P:=by omega
    omega

#print axioms critical_root_even_exit_sharp_budget
end BB6.Agent23RootWall
