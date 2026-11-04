import HighValuationGap
import SmallMods

namespace Agent22Special

/-- Each generic section successor equation forces the precise Fermat
    modulus congruence, without assumptions on v beyond naturalness. -/
theorem generic_eq_mod (j b v : Nat) (hb : 1 ≤ b)
    (heq : ((2:Nat)^(b+1)+1)*v+2*b = 3*2^(j+1)+1) :
    (3*2^(j+1))%((2:Nat)^(b+1)+1) =
      (2*b-1)%((2:Nat)^(b+1)+1) := by
  let m := (2:Nat)^(b+1)+1
  let k := 2*b-1
  have hk : 0 < 2*b := by omega
  have heq' : 3*2^(j+1) = m*v+k := by
    dsimp [m,k] at *
    omega
  rw [heq', Nat.add_mod, Nat.mul_mod_right]
  simp only [Nat.zero_add, Nat.mod_mod]
  rfl

/-- Fully kernel-proved generic valuation exclusion for the progression
    of exceptional odd-cofactor-three targets 3*2^(4k+2). -/
theorem no_generic_target (k b v : Nat) (hb : 1 ≤ b) :
    ((2:Nat)^(b+1)+1)*v+2*b ≠ 3*2^(4*k+3)+1 := by
  by_cases hb5 : 5 ≤ b
  · have he : 4*k+3 = (4*k+2)+1 := by omega
    rw [he]
    exact no_generic_high (4*k+2) b v hb5
  · have hsmall : b=1 ∨ b=2 ∨ b=3 ∨ b=4 := by omega
    intro heq
    have hm := generic_eq_mod (4*k+2) b v hb (by
      have he : 4*k+3=(4*k+2)+1 := by omega
      rw [he] at heq
      exact heq)
    have he : (4*k+2)+1=4*k+3 := by omega
    rw [he] at hm
    rcases hsmall with h|h|h|h
    · subst b
      simp at hm
      exact no_b1 k hm
    · subst b
      simp at hm
      exact no_b2 k hm
    · subst b
      simp at hm
      exact no_b3 k hm
    · subst b
      simp at hm
      exact no_b4 k hm

/-- The valuation-zero generic expression is divisible by 3, while target
    2*(3*2^j)+1 is 1 modulo 3. -/
theorem no_generic_target_any (k b v : Nat) :
    ((2:Nat)^(b+1)+1)*v+2*b ≠ 3*2^(4*k+3)+1 := by
  by_cases hb : b=0
  · subst b
    simp
    omega
  · exact no_generic_target k b v (by omega)

#print axioms no_generic_target_any
#print axioms generic_eq_mod
#print axioms no_generic_target
end Agent22Special
