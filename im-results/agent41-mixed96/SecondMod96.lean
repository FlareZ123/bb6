import Std
namespace A41

theorem pow_even_ge6_mod96 (m : Nat) (hm : 2 ≤ m) :
    2^(2*m+2) % 96 = 64 := by
  obtain ⟨n,hn⟩ : ∃ n, m = n+2 := ⟨m-2, by omega⟩
  subst m
  induction n with
  | zero => decide
  | succ n ih =>
    have hp : 2^(2*(n+1+2)+2) = 4*2^(2*(n+2)+2) := by
      have he : 2*(n+1+2)+2 = 2+(2*(n+2)+2) := by omega
      rw [he,Nat.pow_add]
    rw [hp]
    omega

theorem second_target_5_29_mod96 (j m k : Nat)
    (hj : j%96 = 5) (hm : m%96 = 29)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=13 ∧ k%96=31 := by
  have hm2 : 2 ≤ m := by omega
  have hp := pow_even_ge6_mod96 m hm2
  have hj8 : (j+3)%96=8 := by omega
  have hpmod : (2^(2*m+2)*(j+3))%96=32 := by
    rw [Nat.mul_mod,hp,hj8]
  constructor
  · omega
  · have hr : (k+j+3*m+5)%96=32 := by rw [heq]; exact hpmod
    omega

#print axioms pow_even_ge6_mod96
#print axioms second_target_5_29_mod96
end A41
