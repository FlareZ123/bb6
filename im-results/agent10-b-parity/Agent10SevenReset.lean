import Agent10ModSeven
import Agent10GrowthSource

namespace BB6.Agent10B

theorem G_ne_two_mod3 (z : Nat) : (G z)%3 ≠ 2 := by
  simp only [G]
  omega

theorem iterG_last (n z : Nat) : iterG (n+1) z = G (iterG n z) := by
  have h:=G_iter_add n 1 z
  simpa [iterG] using h

theorem iterG_ne_two_mod3 (n z : Nat) :
    (iterG (n+1) z)%3 ≠ 2 := by
  rw [iterG_last]
  exact G_ne_two_mod3 _

theorem scalarA_ge_three (n : Nat) :
    3 ≤ BB6.OneDim.scalarA n := by
  cases n with
  | zero => decide
  | succ n =>
    let z := BB6.OneDim.iterG (BB6.OneDim.scalarA n) 0
    have hp : z%2 ≤ 1 := by omega
    change 3 ≤ z+9-3*(z%2)
    omega

/-- Every continued scalar reset index is 1 or 3 modulo 6. -/
theorem scalarA_mod6 (n : Nat) :
    BB6.OneDim.scalarA n % 6 = 1 ∨ BB6.OneDim.scalarA n % 6 = 3 := by
  induction n with
  | zero => right; decide
  | succ n ih =>
    let a := BB6.OneDim.scalarA n
    let z := BB6.OneDim.iterG a 0
    have ha : 0 < a := by
      have hg:=scalarA_ge_three n
      omega
    have hg : z%3 ≠2 := by
      have hz : z = iterG a 0 := by
        exact (iterG_eq_source a 0).symm
      rw [hz]
      have heq : a = (a-1)+1 := by omega
      rw [heq]
      exact iterG_ne_two_mod3 (a-1) 0
    have hb : z%2≤1 := by omega
    change (z+9-3*(z%2))%6=1 ∨ (z+9-3*(z%2))%6=3
    omega

/-- The mod-seven power at any reset lies in two explicit residue classes. -/
theorem five_pow_at_reset (n : Nat) :
    (5^(BB6.OneDim.scalarA n))%7 = 5 ∨
    (5^(BB6.OneDim.scalarA n))%7 = 6 := by
  have h := five_pow_mod7_reduced (BB6.OneDim.scalarA n)
  rcases scalarA_mod6 n with hr | hr
  · rw [hr] at h
    left
    simpa using h
  · rw [hr] at h
    right
    simpa using h

/-- Exact scalar orbit/reset congruence independent of the unknown sample bit. -/
theorem scalarA_mod7_link (n : Nat) :
    let a := BB6.OneDim.scalarA n
    let z := BB6.OneDim.iterG a 0
    (BB6.OneDim.scalarA (n+1) + 3*(z%2))%7 = (5^a+1)%7 := by
  let a := BB6.OneDim.scalarA n
  let z := BB6.OneDim.iterG a 0
  have hsrc : z = iterG a 0 := (iterG_eq_source a 0).symm
  have h := G_blank_mod7 a
  rw [←hsrc] at h
  have hb : z%2 ≤ 1 := by omega
  have ha : BB6.OneDim.scalarA (n+1)+3*(z%2)=z+9 := by
    change (z+9-3*(z%2))+3*(z%2)=z+9
    omega
  change (BB6.OneDim.scalarA (n+1) + 3*(z%2))%7 = (5^a+1)%7
  rw [ha]
  omega

/-- Zero sample parity iff the next syntactic reset index is 0 or 6 mod 7. -/
theorem reset_bit_iff_mod7 (n : Nat) :
    let a := BB6.OneDim.scalarA n
    let z := BB6.OneDim.iterG a 0
    (z%2=0) ↔
      ((BB6.OneDim.scalarA (n+1))%7=0 ∨
       (BB6.OneDim.scalarA (n+1))%7=6) := by
  let a := BB6.OneDim.scalarA n
  let z := BB6.OneDim.iterG a 0
  have hlink := scalarA_mod7_link n
  change (BB6.OneDim.scalarA (n+1)+3*(z%2))%7=(5^a+1)%7 at hlink
  have hpow := five_pow_at_reset n
  change (5^a)%7=5 ∨ (5^a)%7=6 at hpow
  have hz : z%2≤1 := by omega
  change z%2=0 ↔
    ((BB6.OneDim.scalarA (n+1))%7=0 ∨
       (BB6.OneDim.scalarA (n+1))%7=6)
  constructor
  · intro hb
    rcases hpow with h5 | h6
    · right
      omega
    · left
      omega
  · intro hr
    rcases hpow with h5 | h6
    · omega
    · omega

#print axioms G_ne_two_mod3
#print axioms scalarA_mod6
#print axioms scalarA_mod7_link
#print axioms reset_bit_iff_mod7
end BB6.Agent10B
