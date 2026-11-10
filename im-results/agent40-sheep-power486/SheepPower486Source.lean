import SheepEvenReachInverse
import SheepPower486NoSource
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace SheepPower486

/-- Authentic blank-even Sheep root exclusion at the sixth 3-adic stratum,
    using the published source's exact inverse split and all-time last-edge theorem. -/
theorem blank_even_cannot_hit_sixth (t : Nat)
    (ht : 1≤t) (ht3 : t%3≠0)
    (ht4 : t%4=0) (ht7 : t%7≠1) (ht9 : t%9≠2) :
    ¬ SheepEven.EvenReach 10 (2^(486*t)) := by
  intro hreach
  have hneq : 2^(486*t)≠10 := by
    have hn : 4≤486*t := by omega
    have hpow : 2^4≤2^(486*t) := Nat.pow_le_pow_right (by decide) hn
    omega
  have hy : 1*(2^(486*t))+0=2^(486*t) := by omega
  rcases SheepEvenReachInverse.blank_even_inverse_cases hreach hneq hy with
    ⟨x,a,h,v,u,hprefix,ha,hv,hvodd,huodd,hxdef,hydef,heq⟩ |
    ⟨x,a,h,u,hprefix,ha,huodd,hxdef,hydef,heq⟩
  · have hgen : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
        =2^(486*t+h+1)+3*3^h := by
      simpa only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using heq
    exact no_inverse_source_cases t h a u v ht ht3 ha ht4 ht7 ht9 hydef (Or.inl hgen)
  · have hspe : 3^h*(3*2^a+a+2)+2^h=2^(486*t+h) := by
      simpa only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using heq
    exact no_inverse_source_cases t h a u 0 ht ht3 ha ht4 ht7 ht9 hydef (Or.inr hspe)

#print axioms blank_even_cannot_hit_sixth
end SheepPower486
