import SheepEvenReachInverse
import SheepPower1458NoSource
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace SheepPower1458
theorem blank_even_cannot_hit_seventh (t : Nat)
    (ht : 1≤t) (ht3 : t%3≠0)
    (ht4 : t%4=0) (ht7 : t%7≠5) (ht9 : t%9≠1) (ht15 : t%15≠8) :
    ¬ SheepEven.EvenReach 10 (2^(1458*t)) := by
  intro hreach
  have hneq : 2^(1458*t)≠10 := by
    have hn : 4≤1458*t := by omega
    have hpow : 2^4≤2^(1458*t) := Nat.pow_le_pow_right (by decide) hn
    omega
  have hy : 1*(2^(1458*t))+0=2^(1458*t) := by omega
  rcases SheepEvenReachInverse.blank_even_inverse_cases hreach hneq hy with
    ⟨x,a,h,v,u,hprefix,ha,hv,hvodd,huodd,hxdef,hydef,heq⟩ |
    ⟨x,a,h,u,hprefix,ha,huodd,hxdef,hydef,heq⟩
  · have hgen : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
        =2^(1458*t+h+1)+3*3^h := by
      simpa only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using heq
    exact no_inverse_source_cases t h a u v ht ht3 ha ht4 ht7 ht9 ht15 hydef (Or.inl hgen)
  · have hspe : 3^h*(3*2^a+a+2)+2^h=2^(1458*t+h) := by
      simpa only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using heq
    exact no_inverse_source_cases t h a u 0 ht ht3 ha ht4 ht7 ht9 ht15 hydef (Or.inr hspe)
theorem blank_even_cannot_hit_seventh_progression (k : Nat) :
    ¬ SheepEven.EvenReach 10 (2^(5832+1837080*k)) := by
  have h := blank_even_cannot_hit_seventh (4+1260*k)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have heq : 1458*(4+1260*k)=5832+1837080*k := by omega
  simpa [heq] using h
#print axioms blank_even_cannot_hit_seventh
#print axioms blank_even_cannot_hit_seventh_progression
end SheepPower1458
