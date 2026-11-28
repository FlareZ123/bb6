import AntiShortTrace
set_option maxHeartbeats 0
namespace BB6.Agent9AntiShortExamples
open BB6.Agent9ReturnGCD BB6.Agent45.DelayedCarry BB6.Agent9AntiShortTrace

/-- Noncoprime negacyclic 9|2^3+1: forbids length 2n+13,
    improving the best cyclic 9|2^6-1 bound 2n+16. -/
theorem no_nine_antishift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+9*2^r+(2*n+13)≤m)
    (hrep : ∀ j<2*n+13,
      bit W (i+9*2^r+j)=
        if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_antishort_repeat hn heven ht i r 9 3 (n+7) flip
  · decide
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 9*(7*2^n+3+1)<2^n*128
    have hpos := Nat.two_pow_pos n
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

/-- Noncoprime negacyclic 27|2^9+1: forbids length 2n+20,
    saving nine bits over the cyclic-order 27|2^18-1 bound. -/
theorem no_twentyseven_antishift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+27*2^r+(2*n+20)≤m)
    (hrep : ∀ j<2*n+20,
      bit W (i+27*2^r+j)=
        if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_antishort_repeat hn heven ht i r 27 9 (n+8) flip
  · decide
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 27*(7*2^n+9+1)<2^n*256
    have hpos := Nat.two_pow_pos n
    have hpow := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

/-- A larger cubic example, 81|2^27+1, with gcd(81,27)=27:
    forbids identical or complemented factors of length 2n+40. -/
theorem no_eightyone_antishift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+81*2^r+(2*n+40)≤m)
    (hrep : ∀ j<2*n+40,
      bit W (i+81*2^r+j)=
        if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_antishort_repeat hn heven ht i r 81 27 (n+10) flip
  · decide
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 81*(7*2^n+27+1)<2^n*1024
    have hpos := Nat.two_pow_pos n
    have hpow := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

#print axioms no_nine_antishift
#print axioms no_twentyseven_antishift
#print axioms no_eightyone_antishift
end BB6.Agent9AntiShortExamples
