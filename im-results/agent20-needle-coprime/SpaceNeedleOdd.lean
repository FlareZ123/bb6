import SpaceNeedleDensity

namespace SpaceNeedlePrime

def fourQ : Nat → Nat
  | 0 => 2
  | n+1 => 16 * fourQ n + 18

def fourExponent (n : Nat) : Nat := 4+4*n

theorem four_identity (n : Nat) :
    2^fourExponent n = 5*fourQ n + 6 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have he : fourExponent (n+1)=fourExponent n+4 := by simp [fourExponent]; omega
    rw [he, Nat.pow_add, ih]
    change (5*fourQ n+6)*16 = 5*(16*fourQ n+18)+6
    omega

theorem four_admissible (n : Nat) : admissibleExponent (fourExponent n) := by
  unfold admissibleExponent
  refine ⟨0, fourQ n, ?_⟩
  rw [four_identity]
  omega

private theorem odd_modulus_hit (m a : Nat) (hm : 0<m) (hodd : m%2=1) :
    ∃ t, (4+4*t)%m=a%m := by
  let u := (m+1)/2
  have hu : 2*u=m+1 := by dsimp [u]; omega
  let z := a + 4*m-4
  have hz : z+4=a+4*m := by dsimp [z]; omega
  have hw : 4*(u*u)*z = z + m*(m+2)*z := by
    have h1 : 4*(u*u)*z = ((2*u)*(2*u))*z := by
      change (2*2)*(u*u)*z = ((2*u)*(2*u))*z
      ac_rfl
    have h2 : (m+1)*(m+1) = 1+m*(m+2) := by simp only [Nat.add_mul,Nat.mul_add]; omega
    rw [h1,hu,h2]
    simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
  let t := (u*u)*z
  have hEq : 4+4*t = a+m*(4+(m+2)*z) := by
    dsimp [t]
    have hmul : 4*((u*u)*z) = 4*(u*u)*z := by simp [Nat.mul_assoc]
    rw [hmul,hw]
    have hmA : m*(m+2)*z = m*((m+2)*z) := by simp [Nat.mul_assoc]
    rw [hmA, Nat.mul_add]
    omega
  refine ⟨t, ?_⟩
  rw [hEq]
  rw [Nat.mul_comm m (4+(m+2)*z)]
  exact Nat.add_mul_mod_self_right a (4+(m+2)*z) m

theorem every_odd_modulus_predecessors (m a bound : Nat)
    (hm : 0 < m) (hodd : m%2=1) :
    ∃ k, bound ≤ k ∧ k%m=a%m ∧ admissibleExponent k := by
  obtain ⟨t,ht⟩ := odd_modulus_hit m a hm hodd
  obtain ⟨k,hb,hmod4,hmodm⟩ :=
    extend_progression 4 4 (bound+4) m (a%m) t (by decide) hm ht
  have hk : fourExponent (k/4-1) = k := by
    have hm_eq := Nat.mod_add_div k 4
    unfold fourExponent
    omega
  refine ⟨k, by omega, hmodm, ?_⟩
  simpa only [hk] using four_admissible (k/4-1)

#print axioms every_odd_modulus_predecessors
end SpaceNeedlePrime
