import Std
namespace BB6.Agent8Zero

private theorem twice_le_two_power (t : Nat) : 2*t ≤ 2^t := by
  cases t with
  | zero => decide
  | succ t =>
      rw [Nat.pow_succ]
      have hlt : t < (2:Nat)^t := Nat.lt_pow_self (by decide)
      omega

/-- Any odd hub whose exact inverse has output zero and whose even-left
successor obeys the reachable power shape has a rigid depth/counter form. -/
theorem zero_even_numeric_rigidity
    (b d t k j : Nat)
    (hb : 8≤b) (hb4 : b%4=0) (hdpos : 0<d)
    (hpower : d+b/2+3=3*2^t)
    (hmass : 2*k+2*t+1=b+d)
    (hreach : 2*k+8=14*2^j) :
    t=j+2 ∧ b=4*(2^j+j) ∧ d+2*j+3=10*2^j := by
  have hbeven : b=2*(b/2) := by omega
  have hLow : 7*2^j+t≤3*2^t := by omega
  have hUpper : 3*2^t+8≤14*2^j+2*t := by omega
  have hTge : j+2≤t := by
    by_cases h : j+2≤t
    · exact h
    · have htj : t≤j+1 := by omega
      have hmon : (2:Nat)^t≤2^(j+1) := Nat.pow_le_pow_right (by decide) htj
      have hpow2 : (2:Nat)^(j+1)=2*2^j := by
        rw [Nat.pow_succ]
        omega
      omega
  have hTle : t≤j+2 := by
    by_cases h : t≤j+2
    · exact h
    · have hbig : j+3≤t := by omega
      have hmon : (2:Nat)^(j+3)≤2^t := Nat.pow_le_pow_right (by decide) hbig
      have hpow8 : (2:Nat)^(j+3)=8*2^j := by
        rw [Nat.pow_add]
        have h8 : (2:Nat)^3=8 := by decide
        rw [h8]
        omega
      have hTpow : 2*t≤2^t := twice_le_two_power t
      omega
  have hT : t=j+2 := by omega
  have hpow4 : (2:Nat)^(j+2)=4*2^j := by
    rw [Nat.pow_add]
    have h4 : (2:Nat)^2=4 := by decide
    rw [h4]
    omega
  subst t
  constructor
  · rfl
  constructor
  · omega
  · omega

#print axioms BB6.Agent8Zero.zero_even_numeric_rigidity
end BB6.Agent8Zero
