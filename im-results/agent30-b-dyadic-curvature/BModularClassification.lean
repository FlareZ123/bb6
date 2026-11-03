import BModularSource
import Agent10ModSeven

namespace BB6.Agent30B

private theorem affine_mod7_from_shifted (n z f : Nat)
    (h : (f+8)%7 = (5^n*(z+8))%7) :
    f%7 = (5^n*z+(8*5^n+6))%7 := by
  have hadded : (f+14)%7 = (5^n*(z+8)+6)%7 := by
    calc
      (f+14)%7 = ((f+8)+6)%7 := by omega
      _ = (((f+8)%7)+6)%7 := (Nat.mod_add_mod (f+8) 7 6).symm
      _ = (((5^n*(z+8))%7)+6)%7 := by rw [h]
      _ = (5^n*(z+8)+6)%7 := Nat.mod_add_mod _ 7 6
  have htarget : 5^n*(z+8)+6=5^n*z+(8*5^n+6) := by
    simp [Nat.mul_add, Nat.mul_comm, Nat.add_assoc]
  calc
    f%7 = (f+14)%7 := by omega
    _ = (5^n*(z+8)+6)%7 := hadded
    _ = (5^n*z+(8*5^n+6))%7 := by rw [htarget]

private theorem divisors_of_seven (m : Nat) (hm:0<m) (hd:m∣7) :
    m=1 ∨ m=7 := by
  have hle : m≤7 := Nat.le_of_dvd (by decide) hd
  have hc : m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 ∨ m=6 ∨ m=7 := by
    omega
  rcases hc with h | h | h | h | h | h | h <;>
    subst m <;> simp_all

theorem source_affine_quotients_iff (n m : Nat) (hn:0<n) (hm:0<m) :
    (∃ a b : Nat,
       ∀ z, (BB6.OneDim.iterG n z)%m=(a*z+b)%m) ↔
      m=1 ∨ m=7 := by
  constructor
  · rintro ⟨a,b,h⟩
    obtain ⟨k,hk⟩ : ∃ k, n=k+1 := ⟨n-1, by omega⟩
    subst n
    exact divisors_of_seven m hm
      (source_affine_modulus_divides_seven k m a b h)
  · intro h
    rcases h with rfl | rfl
    · exact ⟨0,0, by intro z; omega⟩
    · refine ⟨5^n,8*5^n+6, ?_⟩
      intro z
      apply affine_mod7_from_shifted n z (BB6.OneDim.iterG n z)
      have heq := BB6.Agent10B.iterG_eq_source n z
      rw [←heq]
      exact BB6.Agent10B.G_mod7_iter n z

#print axioms source_affine_quotients_iff

end BB6.Agent30B
