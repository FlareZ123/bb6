import Lean.Elab.Tactic.Omega

namespace BB6.PrimitiveRankRigidity

def weight3 (u v w a k c : Nat) : Nat := u*a+v*k+w*c

/-- Three infinite explicit section transitions force the exact linear ratio. -/
theorem three_families_force (u v w : Nat)
    (hsweep : u+4*w ≤ v+3*w)
    (hzero : ∀ k, v*k ≤ u+w*(2*k+2))
    (heven : ∀ j, v*(2*j)+4*w ≤ u*(4*j+2)+2*v+w) :
    w=u ∧ v=2*u := by
  have hlow : u+w≤v := by omega
  have hv2w : v≤2*w := by
    by_cases hgt : 2*w<v
    · let k : Nat := u+2*w+1
      have hh := hzero k
      have hcoef : 2*w+1≤v := by omega
      have hmul := Nat.mul_le_mul_right k hcoef
      have hmul' : 2*(w*k)+k ≤ v*k := by
        simpa only [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, Nat.mul_comm w 2] using hmul
      have hh' : v*k≤u+2*(w*k)+2*w := by
        calc
          v*k≤u+w*(2*k+2) := hh
          _ = u+2*(w*k)+2*w := by
            simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] <;> omega
      have hk : u+2*w<k := by dsimp [k]; omega
      omega
    · omega
  have hv2u : v≤2*u := by
    by_cases hgt : 2*u<v
    · let j : Nat := u+v+1
      have hh := heven j
      have hcoef : 2*u+1≤v := by omega
      have hmul := Nat.mul_le_mul_right j hcoef
      have hmul' : 2*(u*j)+j ≤ v*j := by
        simpa only [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, Nat.mul_comm u 2] using hmul
      have hh' : 2*(v*j)+4*w ≤ 4*(u*j)+2*u+2*v+w := by
        calc
          2*(v*j)+4*w = v*(2*j)+4*w := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ u*(4*j+2)+2*v+w := hh
          _ = 4*(u*j)+2*u+2*v+w := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      have hj : u+v<j := by dsimp [j]; omega
      omega
    · omega
  constructor <;> omega

/-- Every globally nondecreasing nonnegative integral linear primitive rank
is a scalar multiple of a+2k+c, provided the three source transition
families and canonical rank monotonicity. -/
theorem unique_linear_primitive
    (f : Nat × Nat × Nat → Option (Nat × Nat × Nat))
    (hrank : ∀ a k c x y z, f (a,k,c)=some (x,y,z) → a+2*k+c ≤ x+2*y+z)
    (hsweep : f (1,0,4)=some (0,1,3))
    (hzero : ∀ k, f (0,k,0)=some (1,0,2*k+2))
    (heven : ∀ j, f (0,2*j,4)=some (4*j+2,2,1))
    (u v w : Nat) :
    (∀ a k c x y z, f (a,k,c)=some (x,y,z) →
      weight3 u v w a k c ≤ weight3 u v w x y z)
      ↔ w=u ∧ v=2*u := by
  constructor
  · intro hmono
    have hs : u+4*w≤v+3*w := by
      have h := hmono 1 0 4 0 1 3 hsweep
      simpa [weight3,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
    have hz : ∀ k, v*k≤u+w*(2*k+2) := by
      intro k
      have h := hmono 0 k 0 1 0 (2*k+2) (hzero k)
      simpa [weight3] using h
    have he : ∀ j, v*(2*j)+4*w≤u*(4*j+2)+2*v+w := by
      intro j
      have h := hmono 0 (2*j) 4 (4*j+2) 2 1 (heven j)
      simpa [weight3,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
    exact three_families_force u v w hs hz he
  · rintro ⟨hw,hv⟩ a k c x y z hedge
    have h := hrank a k c x y z hedge
    have hscaled := Nat.mul_le_mul_left u h
    dsimp [weight3]
    rw [hw,hv]
    calc
      u*a+(2*u)*k+u*c = u*(a+2*k+c) := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _ ≤ u*(x+2*y+z) := hscaled
      _ = u*x+(2*u)*y+u*z := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- No nonnegative linear primitive potential can strictly increase on
every successful transition: the sweep always preserves the unique rank. -/
theorem no_strict_linear_primitive
    (f : Nat × Nat × Nat → Option (Nat × Nat × Nat))
    (hrank : ∀ a k c x y z, f (a,k,c)=some (x,y,z) → a+2*k+c ≤ x+2*y+z)
    (hsweep : f (1,0,4)=some (0,1,3))
    (hzero : ∀ k, f (0,k,0)=some (1,0,2*k+2))
    (heven : ∀ j, f (0,2*j,4)=some (4*j+2,2,1))
    (u v w : Nat) :
    ¬ (∀ a k c x y z, f (a,k,c)=some (x,y,z) →
      weight3 u v w a k c < weight3 u v w x y z) := by
  intro hstrict
  have hmono := (unique_linear_primitive f hrank hsweep hzero heven u v w).mp
    (fun a k c x y z hh => Nat.le_of_lt (hstrict a k c x y z hh))
  rcases hmono with ⟨hw,hv⟩
  have hh := hstrict 1 0 4 0 1 3 hsweep
  simp [weight3,hw,hv] at hh
  omega

#print axioms three_families_force
#print axioms unique_linear_primitive
#print axioms no_strict_linear_primitive
end BB6.PrimitiveRankRigidity
