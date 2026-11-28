import Std
namespace BB6.Agent32SignedRayBlock

/-- A logarithmically bounded signed form has a constant ternary high block. -/
theorem small_signed_block (z b d : Int) (_hb : 0 < b) (hd : 0 < d)
    (hlo : -b < z) (hhi : z < b) :
    (z / b) % d = 0 ∨ (z / b) % d = d-1 := by
  by_cases h : 0 ≤ z
  · left
    rw [Int.ediv_eq_zero_of_lt h hhi]
    simp
  · right
    rw [Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)]
    have he : d-1 + d * (-1) = (-1 : Int) := by omega
    exact (Int.ediv_emod_unique hd).2 ⟨he, by omega, by omega⟩ |>.2

/-- The two-coordinate signed representation, including its sector offset. -/
theorem ray_form (P Q L m gamma x y : Int)
    (hx : x = 2*(L-4*m)-gamma) (hy : y = 6*m) :
    3*P*x + (4*P-Q)*y + 3*P*gamma = 6*(P*L-Q*m) := by
  subst x y
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  simp only [show (2 : Int)*3=6 by decide, show (3 : Int)*4=12 by decide, show (2 : Int)*12=24 by decide, show (4 : Int)*6=24 by decide]
  omega

/-- Quotient of a signed linear form can be computed from the high coordinates
    and a single exact low-digit carry, without an approximation. -/
def carry (A B G x y b : Int) : Int := (A*(x%b)+B*(y%b)+G)/b

theorem quotient_form (A B G x y b : Int) (hb : b ≠ 0) :
    (A*x+B*y+G)/b = A*(x/b)+B*(y/b)+carry A B G x y b := by
  have hx := Int.emod_add_mul_ediv x b
  have hy := Int.emod_add_mul_ediv y b
  have he : A*x+B*y+G = (A*(x%b)+B*(y%b)+G) + b*(A*(x/b)+B*(y/b)) := by
    conv => lhs; rw [← hx, ← hy]
    simp only [Int.mul_add, Int.mul_left_comm]
    omega
  rw [he, Int.add_mul_ediv_left _ _ hb]
  unfold carry
  omega

/-- The low-block remainder extends by one ordinary base-three digit. -/
theorem low_extend (x b : Int) (hb : 0 < b) :
    x%(b*3) = x%b + b*((x/b)%3) := by
  have h3 : (0 : Int) < 3 := by decide
  have h := Int.emod_add_mul_ediv x b
  have h' := Int.emod_add_mul_ediv (x/b) 3
  have hrem := Int.emod_nonneg x (by omega : b ≠ 0)
  have hrem' := Int.emod_lt_of_pos x hb
  have hdig := Int.emod_nonneg (x/b) (by decide : (3:Int) ≠ 0)
  have hdig' := Int.emod_lt_of_pos (x/b) h3
  have hn : 0 ≤ b*((x/b)%3) := Int.mul_nonneg (by omega) hdig
  have hu : b*((x/b)%3) ≤ b*2 := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have he : x%b + b*((x/b)%3) + (b*3)*(x/b/3) = x := by
    have hm := congrArg (b * ·) h'
    simp only [Int.mul_add, ← Int.mul_assoc] at hm
    omega
  exact ((Int.ediv_emod_unique (by omega : 0<b*3)).2 ⟨he, by omega, by omega⟩).2

/-- One synchronized ternary input pair advances the authentic scalar carry. -/
theorem carry_next (A B G x y b : Int) (hb : 0 < b) :
    carry A B G x y (b*3) = (A*((x/b)%3)+B*((y/b)%3)+carry A B G x y b)/3 := by
  unfold carry
  rw [low_extend x b hb,low_extend y b hb,Int.ediv_mul_of_nonneg (by omega : 0≤b)]
  have he : A*(x%b+b*((x/b)%3))+B*(y%b+b*((y/b)%3))+G =
      (A*(x%b)+B*(y%b)+G)+b*(A*((x/b)%3)+B*((y/b)%3)) := by
    simp only [Int.mul_add,Int.mul_left_comm]
    omega
  rw [he,Int.add_mul_ediv_left _ _ (by omega : b ≠ 0)]
  congr 1
  omega

/-- Any strip exclusion can be certified by a finite nonconstant signed block. -/
theorem excludes_strip (z lo hi b d : Int) (hb : 0 < b) (hd : 0 < d)
    (hlo : lo < b) (hhi : hi < b)
    (hzero : (z/b)%d ≠ 0) (htwo : (z/b)%d ≠ d-1) : z < -lo ∨ hi < z := by
  by_cases h : z < -lo
  · exact Or.inl h
  by_cases h' : hi < z
  · exact Or.inr h'
  exfalso
  rcases small_signed_block z b d hb hd (by omega) (by omega) with he|he
  · exact hzero he
  · exact htwo he

#print axioms carry_next
#print axioms excludes_strip
end BB6.Agent32SignedRayBlock
