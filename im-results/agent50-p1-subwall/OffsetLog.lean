import SubwallLog

namespace BB6.Agent50OffsetLog
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent50SubwallLog

/-- A dyadic inverse word needs logarithmic cost throughout the
    arbitrary-offset subwall, with no bound on the width r or inverse cost m. -/
theorem word_offset_logarithmic_gap
    {n r K D m A T : Nat}
    (hn : 14 ≤ n) (hK : K+n+3=7*2^n)
    (hword : OddWord K D m A T)
    (hsub : K ≤ D+3*m+2*(n+r)+4) :
    2^(n-m) < n+r := by
  by_cases hm : n ≤ m
  · have hzero : n-m=0 := by omega
    simp only [hzero]
    simp
    omega
  · have hless : m < n := by omega
    let k := n-m
    have hnk : n=m+k := by dsimp [k]; omega
    have hP : 2^n=2^m*2^k := by
      rw [hnk]
      exact Nat.pow_add 2 m k
    have hlin : n+4 ≤ 2^n := n_plus_four_le_pow n (by omega)
    have hcoeff : 3*m+2*(n+r)+4 ≤ 5*n+2*r+1 := by omega
    have hc : K ≤ 1+2^m*(3*m+2*(n+r)+4) :=
      word_subwall_cost_necessary (n:=n+r) hword hsub
    have hbound : 7*2^n ≤ 2^n+2^m*(5*n+2*r+1) := by
      have hcoeffmul :
          2^m*(3*m+2*(n+r)+4) ≤ 2^m*(5*n+2*r+1) :=
        Nat.mul_le_mul_left (2^m) hcoeff
      omega
    have hc6 : 6*2^n ≤ 2^m*(5*n+2*r+1) := by omega
    have hmult :
        2^m*(6*2^k) ≤ 2^m*(5*n+2*r+1) := by
      calc
        _ = 6*2^n := by rw [hP]; ac_rfl
        _ ≤ _ := hc6
    have hpos : 0<2^m := Nat.pow_pos (by decide)
    have hkbound : 6*2^k ≤ 5*n+2*r+1 :=
      Nat.le_of_mul_le_mul_left hmult hpos
    have hkn : 2^k < n+r := by omega
    simpa only [show n-m=k by rfl] using hkn

/-- True original P1 inverse histories have a logarithmic cost gap for
    arbitrary nonnegative left offset r. -/
theorem source_critical_offset_logarithmic_gap
    (n r b d m : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hsub : b ≤ 4*(m+n+r)) :
    2^(n-m) < n+r := by
  let K : Nat := 7*2^n-n-3
  have hdom : n+4 ≤ 2^n := n_plus_four_le_pow n (by omega)
  have hK : K+n+3=7*2^n := by dsimp [K]; omega
  have hroot : (14*2^n-2*n-16)+10=2*K := by
    dsimp [K]
    omega
  obtain ⟨D,A,T,hdD,hbalance,hword⟩ :=
    source_oddcone_has_word (14*2^n-2*n-16) K b d m hroot hcone
  have hsubK : K ≤ D+3*m+2*(n+r)+4 := by omega
  exact word_offset_logarithmic_gap hn hK hword hsubK

#print axioms BB6.Agent50OffsetLog.word_offset_logarithmic_gap
#print axioms BB6.Agent50OffsetLog.source_critical_offset_logarithmic_gap

end BB6.Agent50OffsetLog
