import ExceptionalExp
import OddWordSourceBridge

namespace BB6.Agent8Exceptional
open BB6.Agent28 BB6.Agent1Quarter

/-- Source-connected necessary exponential cost constraint at the true
    critical P1 inverse-cone exceptional coordinate d=5. -/
theorem source_critical_odd_d5_exponential_cost
    (n b d m : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hd : d=5) :
    6*2^n ≤ (n+m+3)*2^(m+1-n) := by
  let K : Nat := 7*2^n-n-3
  have hlin : n ≤ 2^n := n_le_pow n
  have h16 : (2:Nat)^4 ≤ 2^n :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h16' : 16 ≤ (2:Nat)^n := by simpa using h16
  have hK : K+n+3=7*2^n := by dsimp [K]; omega
  have hroot : (14*2^n-2*n-16)+10=2*K := by dsimp [K]; omega
  obtain ⟨D,A,T,hdD,hbalance,hword⟩ :=
    source_oddcone_has_word (14*2^n-2*n-16) K b d m hroot hcone
  have hD : D=2 := by omega
  subst D
  exact OddWord.exceptional_exponential_cost n K m A T hn hK hword

#print axioms BB6.Agent8Exceptional.source_critical_odd_d5_exponential_cost
end BB6.Agent8Exceptional
