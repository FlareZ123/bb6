import DyadicCheckerDuality
import DyadicRays

namespace BB6.Agent21Duality
open BB6.Agent21Dyadic
open BB6.Agent42ModularCone

/-- An all-time asymptotic theorem about an *executable* inverse exclusion
    algorithm: one binary modulus works uniformly over EVERY nonnegative
    even-left/odd-right affine ray. Outside at most a 1/d fraction of
    parameter residues the existing modular checker certifies exclusion.
    This concerns all candidate residues, not the trivially sparse
    deterministic stopping set. -/
theorem checker_dense_on_even_odd_rays (d : Nat) (hd : 0<d) :
    ∃ n : Nat, ∀ x y a b : Nat, ∃ R : List Int,
      d*R.length≤2^n ∧
      ∀ t : Nat,
        excluded n
          ⟨((x+2*a*t:Nat):Int),((y+(2*b+1)*t:Nat):Int)⟩=false →
        (t:Int)%BB6.Agent21Dyadic.P n∈R := by
  obtain ⟨n,hn⟩ := sparse_cover d hd
  refine ⟨n,?_⟩
  intro x y a b
  obtain ⟨R,hR,hcover⟩ :=
    hn (rayAffine x y a b) (ray_admissible x y a b)
  refine ⟨R,hR,?_⟩
  intro t hno
  let p : Pair :=
    ⟨((x+2*a*t:Nat):Int),((y+(2*b+1)*t:Nat):Int)⟩
  have hno' : excluded n p=false := hno
  have hopen : OpenAt (signedS p.x p.y) (signedZ p.x p.y) n := by
    by_cases ho : OpenAt (signedS p.x p.y) (signedZ p.x p.y) n
    · exact ho
    · have hh := (excluded_open_duality n p).mpr ho
      rw [hh] at hno'
      cases hno'
  have hr := ray_coords x y a b t
  have ho : OpenAt (mass (rayAffine x y a b) (t:Int))
      (norm (rayAffine x y a b) (t:Int)) n := by
    change OpenAt (S (x+2*a*t) (y+(2*b+1)*t))
        (Z (x+2*a*t) (y+(2*b+1)*t)) n at hopen
    rw [hr.1,hr.2] at hopen
    exact hopen
  exact hcover (t:Int) ho

#print axioms checker_dense_on_even_odd_rays
end BB6.Agent21Duality
