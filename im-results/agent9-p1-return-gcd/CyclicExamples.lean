import CyclicTraceShort
set_option maxHeartbeats 0

namespace BB6.Agent9CyclicExamples
open BB6.Agent9ReturnGCD BB6.Agent45.DelayedCarry BB6.Agent9CyclicTraceShort

/-- A non-coprime example (gcd(9,6)=3): no equal or opposite
    delayed-carry factors at shift 9*2^r of length 2n+16. -/
theorem no_nine_shift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+9*2^r+(2*n+16)≤m)
    (hrep : ∀ j<2*n+16,
      bit W (i+9*2^r+j)=
        if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_short_repeat hn heven ht i r 9 6 (n+7) flip
  · decide
  · omega
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 9*(7*2^n+6+1)<2^n*128
    have hpos := Nat.two_pow_pos n
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

/-- The higher non-coprime example gcd(27,18)=9: the one-period
    bound saves 14 selected bits over a 2K-return obstruction. -/
theorem no_twentyseven_shift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+27*2^r+(2*n+29)≤m)
    (hrep : ∀ j<2*n+29,
      bit W (i+27*2^r+j)=
        if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_short_repeat hn heven ht i r 27 18 (n+8) flip
  · decide
  · omega
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 27*(7*2^n+18+1)<2^n*256
    have hpos := Nat.two_pow_pos n
    have hpow := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

/-- Small factor of the 23rd Mersenne number: 47*2^r shifts
    forbid either parity of equality for 2n+35 bits, shortening the
    old 2n+53 order-return bound by 18 bits. -/
theorem no_fortyseven_shift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+47*2^r+(2*n+35)≤m)
    (hrep : ∀ j<2*n+35,
      bit W (i+47*2^r+j)=
        if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_short_repeat hn heven ht i r 47 23 (n+9) flip
  · decide
  · omega
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 47*(7*2^n+23+1)<2^n*512
    have hpos := Nat.two_pow_pos n
    have hpow := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

#print axioms no_nine_shift
#print axioms no_twentyseven_shift
#print axioms no_fortyseven_shift
end BB6.Agent9CyclicExamples
