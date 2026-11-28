import AntiGenericTrace
set_option maxHeartbeats 0
namespace BB6.Agent9AntiFermatTrace
open BB6.Agent9ReturnGCD BB6.Agent45.DelayedCarry BB6.Agent9AntiGenericTrace

/-- The first Fermat prime beyond five: forbidden 17·2^r anti/equal
    factors at length 2n+14 (versus the previous order bound 2n+23). -/
theorem trace_no_17_shift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+17*2^r+(2*n+14)≤m)
    (hrep : ∀ j<2*n+14,
      bit W (i+17*2^r+j)=if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_negacyclic_repeat hn heven ht i r 17 4 (n+7) flip
  · decide
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 17*(7*2^n+4+1)<2^n*128
    have H := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

/-- The order-five modulus eleven, with 2^5=-1 (mod 11). -/
theorem trace_no_11_shift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+11*2^r+(2*n+15)≤m)
    (hrep : ∀ j<2*n+15,
      bit W (i+11*2^r+j)=if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_negacyclic_repeat hn heven ht i r 11 5 (n+7) flip
  · decide
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 11*(7*2^n+5+1)<2^n*128
    have H := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

/-- Seven-step antiperiod at modulus 43, a factor of 2^7+1. -/
theorem trace_no_43_shift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+43*2^r+(2*n+19)≤m)
    (hrep : ∀ j<2*n+19,
      bit W (i+43*2^r+j)=if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_negacyclic_repeat hn heven ht i r 43 7 (n+9) flip
  · decide
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 43*(7*2^n+7+1)<2^n*512
    have H := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

/-- Fermat modulus 257: the first member with an eight-position
    antiperiod. Its dyadic-separated factors have length < 2n+22. -/
theorem trace_no_257_shift {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r : Nat) (flip : Bool)
    (hp : i+257*2^r+(2*n+22)≤m)
    (hrep : ∀ j<2*n+22,
      bit W (i+257*2^r+j)=if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  apply trace_no_odd_negacyclic_repeat hn heven ht i r 257 8 (n+11) flip
  · decide
  · decide
  · decide
  · unfold total
    rw [Nat.pow_add]
    change 257*(7*2^n+8+1)<2^n*2048
    have H := Nat.lt_two_pow_self (n:=n)
    omega
  · omega
  · intro j hj
    have hh := hrep j (by omega)
    simpa only [Nat.mul_comm] using hh

#print axioms trace_no_17_shift
#print axioms trace_no_11_shift
#print axioms trace_no_43_shift
#print axioms trace_no_257_shift
end BB6.Agent9AntiFermatTrace
