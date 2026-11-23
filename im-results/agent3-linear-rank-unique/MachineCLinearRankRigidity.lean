import Lean.Elab.Tactic.Omega

namespace BB6.LinearRankRigidity

def weight (u v a k : Nat) : Nat := u*a + v*k

/-- Two explicit infinite transition families force the rank weight v=2u. -/
theorem two_families_force_ratio (u v : Nat)
    (hdir : ∀ k, 1 ≤ k → u*(2*k)+v*k ≤ v*(2*k+2))
    (hbounce : ∀ k, 1 ≤ k →
       u*(2*k+1)+v*(k+1) ≤ u*(4*k+2)+v*3) :
    v = 2*u := by
  by_cases heq : v = 2*u
  · exact heq
  · by_cases hlt : v < 2*u
    · let k : Nat := 2*v+1
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hh := hdir k hk
      have hcoef : v+1 ≤ 2*u := by omega
      have hmul := Nat.mul_le_mul_right k hcoef
      have hmul' : v*k+k ≤ 2*(u*k) := by
        simpa only [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, Nat.mul_comm u 2] using hmul
      have hh' : 2*(u*k)+v*k ≤ 2*(v*k)+2*v := by
        calc
          2*(u*k)+v*k = u*(2*k)+v*k := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ v*(2*k+2) := hh
          _ = 2*(v*k)+2*v := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      have hlarge : 2*v < k := by dsimp [k]; omega
      omega
    · have hgt : 2*u+1 ≤ v := by omega
      let k : Nat := u+2*v+1
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hh := hbounce k hk
      have hmul := Nat.mul_le_mul_right k hgt
      have hmul' : 2*(u*k)+k ≤ v*k := by
        simpa only [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, Nat.mul_comm u 2] using hmul
      have hh' : 2*(u*k)+u+v*k+v ≤ 4*(u*k)+2*u+3*v := by
        calc
          2*(u*k)+u+v*k+v = u*(2*k+1)+v*(k+1) := by
            simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] <;> omega
          _ ≤ u*(4*k+2)+v*3 := hh
          _ = 4*(u*k)+2*u+3*v := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      have hlarge : u+2*v < k := by dsimp [k]; omega
      omega

/-- Among nonnegative integral linear ranks, only multiples of a+2k
are nondecreasing on all source transitions of such a section. -/
theorem unique_linear_nondecrease
    (f : Nat × Nat → Option (Nat × Nat))
    (hrank : ∀ a k x y, f (a,k)=some (x,y) → a+2*k < x+2*y)
    (hdir : ∀ k, 1 ≤ k → f (2*k,k)=some (0,2*k+2))
    (hbounce : ∀ k, 1 ≤ k → f (2*k+1,k+1)=some (4*k+2,3))
    (u v : Nat) :
    (∀ a k x y, f (a,k)=some (x,y) → weight u v a k ≤ weight u v x y)
      ↔ v=2*u := by
  constructor
  · intro hmono
    have hfirst : ∀ k, 1≤k → u*(2*k)+v*k ≤ v*(2*k+2) := by
      intro k hk
      have h := hmono (2*k) k 0 (2*k+2) (hdir k hk)
      simpa [weight] using h
    have hsecond : ∀ k, 1≤k →
        u*(2*k+1)+v*(k+1) ≤ u*(4*k+2)+v*3 := by
      intro k hk
      simpa [weight] using hmono (2*k+1) (k+1) (4*k+2) 3 (hbounce k hk)
    exact two_families_force_ratio u v hfirst hsecond
  · intro hv a k x y hedge
    have hinc := hrank a k x y hedge
    have hscaled := Nat.mul_le_mul_left u (Nat.le_of_lt hinc)
    dsimp [weight]
    rw [hv]
    calc
      u*a+(2*u)*k = u*(a+2*k) := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _ ≤ u*(x+2*y) := hscaled
      _ = u*x+(2*u)*y := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- The globally strictly growing linear ranks are precisely positive
scalar multiples of a+2k. -/
theorem unique_linear_strict
    (f : Nat × Nat → Option (Nat × Nat))
    (hrank : ∀ a k x y, f (a,k)=some (x,y) → a+2*k < x+2*y)
    (hdir : ∀ k, 1 ≤ k → f (2*k,k)=some (0,2*k+2))
    (hbounce : ∀ k, 1 ≤ k → f (2*k+1,k+1)=some (4*k+2,3))
    (u v : Nat) :
    (∀ a k x y, f (a,k)=some (x,y) → weight u v a k < weight u v x y)
      ↔ 0<u ∧ v=2*u := by
  constructor
  · intro h
    have hv := (unique_linear_nondecrease f hrank hdir hbounce u v).mp
      (fun a k x y hedge => Nat.le_of_lt (h a k x y hedge))
    have hu : 0<u := by
      by_cases hz : u=0
      · have hv0 : v=0 := by omega
        have hh := h 2 1 0 4 (hdir 1 (by omega))
        simp [weight,hz,hv0] at hh
      · omega
    exact ⟨hu,hv⟩
  · rintro ⟨hu,hv⟩ a k x y hedge
    have hinc := hrank a k x y hedge
    have hscaled := Nat.mul_lt_mul_of_pos_left hinc hu
    dsimp [weight]
    rw [hv]
    calc
      u*a+(2*u)*k = u*(a+2*k) := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _ < u*(x+2*y) := hscaled
      _ = u*x+(2*u)*y := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

#print axioms two_families_force_ratio
#print axioms unique_linear_nondecrease
#print axioms unique_linear_strict
end BB6.LinearRankRigidity
