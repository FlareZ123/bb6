import DyadicRows

namespace BB6.Agent21Dyadic

/-- A monotone affine ray whose left increment is even and whose right
increment is odd. The normalized inverse-word coordinates have the
admissible odd congruence slope, uniformly in all four parameters. -/
def rayAffine (x y a b : Nat) : Affine :=
  ⟨S x y, -2*((a:Int)+2*(b:Int)+1), Z x y, -(a:Int)⟩

theorem ray_admissible (x y a b : Nat) : Admissible (rayAffine x y a b) := by
  unfold Admissible rayAffine
  dsimp
  omega

private theorem cast_ray_x (x a t : Nat) :
    ((x+2*a*t:Nat):Int)=(x:Int)+2*((a:Int)*(t:Int)) := by
  simp only [Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Int.mul_assoc]

private theorem cast_ray_y (y b t : Nat) :
    ((y+(2*b+1)*t:Nat):Int)=(y:Int)+(2*(b:Int)+1)*(t:Int) := by
  simp only [Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]

private theorem ray_product (a b t : Nat) :
    (-2*((a:Int)+2*(b:Int)+1))*(t:Int) =
      -2*((a:Int)*(t:Int))-4*((b:Int)*(t:Int))-2*(t:Int) := by
  have h : ((a:Int)+2*(b:Int)+1)*(t:Int) =
      (a:Int)*(t:Int)+2*((b:Int)*(t:Int))+(t:Int) := by
    rw [Int.add_mul, Int.add_mul, Int.mul_assoc, Int.one_mul]
  rw [show (-2*((a:Int)+2*(b:Int)+1))*(t:Int) =
    -2*(((a:Int)+2*(b:Int)+1)*(t:Int)) by rw [Int.mul_assoc]]
  rw [h]
  omega

theorem ray_coords (x y a b t : Nat) :
    S (x+2*a*t) (y+(2*b+1)*t)=mass (rayAffine x y a b) t ∧
    Z (x+2*a*t) (y+(2*b+1)*t)=norm (rayAffine x y a b) t := by
  have hx := cast_ray_x x a t
  have hy := cast_ray_y y b t
  have hprod := ray_product a b t
  have hmult : (2*(b:Int)+1)*(t:Int) =
      2*((b:Int)*(t:Int))+(t:Int) := by
    rw [Int.add_mul, Int.mul_assoc, Int.one_mul]
  have hs : S (x+2*a*t) (y+(2*b+1)*t)=mass (rayAffine x y a b) t := by
    change -((x+2*a*t:Nat):Int)-2*((y+(2*b+1)*t:Nat):Int) =
      (-(x:Int)-2*(y:Int)) + (-2*((a:Int)+2*(b:Int)+1))*(t:Int)
    rw [hx, hy, hmult, hprod]
    omega
  constructor
  · exact hs
  · have heven : (-2*((a:Int)+2*(b:Int)+1))*(t:Int) =
          2*(-(((a:Int)+2*(b:Int)+1)*(t:Int))) := by
        rw [Int.mul_assoc]
        omega
    have hp : parity (S (x+2*a*t) (y+(2*b+1)*t))=parity (S x y) := by
      rw [hs]
      change (S x y + (-2*((a:Int)+2*(b:Int)+1))*(t:Int)) % 2 = (S x y)%2
      rw [heven]
      omega
    have hz1 := twice_Z (x+2*a*t) (y+(2*b+1)*t)
    have hz0 := twice_Z x y
    rw [hp] at hz1
    rw [hx] at hz1
    change Z (x+2*a*t) (y+(2*b+1)*t)=Z x y-(a:Int)*(t:Int)
    omega

/-- One universal dyadic precision works for every nonnegative affine ray
    (x+2at,y+(2b+1)t). At that precision the reachable indices occupy
    at most a 1/d fraction of residue classes, above the universal height. -/
theorem ray_sparse (reach : Nat→Nat→Prop) (parent : ParentLaw reach)
    (d : Nat) (hd : 0<d) :
    ∃ n, ∀ x y a b : Nat, ∃ R : List Int, d*R.length≤2^n ∧
      ∀ t : Nat, Large (n+2) (y+(2*b+1)*t) →
        reach (x+2*a*t) (y+(2*b+1)*t) → (t:Int)%P n∈R := by
  obtain ⟨n,hn⟩ := sparse_cover d hd
  refine ⟨n,?_⟩
  intro x y a b
  obtain ⟨R,hR,hcover⟩ := hn (rayAffine x y a b) (ray_admissible x y a b)
  refine ⟨R,hR,?_⟩
  intro t ht hr
  have ho := reach_open reach parent n (x+2*a*t) (y+(2*b+1)*t) ht hr
  obtain ⟨hs,hz⟩ := ray_coords x y a b t
  rw [hs,hz] at ho
  exact hcover (t:Int) ho

#print axioms ray_sparse
end BB6.Agent21Dyadic
