import DyadicCheckerDensity
import ModularConeSource

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone

/-- A single original-source, executable, all-ray exclusion theorem. For
    every target density 1-1/d there is a common binary precision n such
    that, outside at most 2^n/d residue classes on EVERY even-left/odd-right
    affine ray, the actual unchanged Machine C section state is provably
    unreachable whenever its right counter satisfies the checker's soundness
    height condition. The excluded predicate itself is executable and its
    exact finite-word semantics are proved in DyadicCheckerDuality.

    This is an asymptotic algorithmic certificate theorem, NOT an all-time
    decision of the blank Machine C orbit or of BB(6). -/
theorem source_checker_dense_on_even_odd_rays (d : Nat) (hd : 0<d) :
    ∃ n : Nat, ∀ x y a b : Nat, ∃ R : List Int,
      d*R.length≤2^n ∧ ∀ t : Nat,
        Large n (y+(2*b+1)*t) →
        (t:Int)%BB6.Agent21Dyadic.P n∉R →
        ¬BB6.Agent3.CReach (x+2*a*t) (y+(2*b+1)*t) := by
  obtain ⟨n,hn⟩ := checker_dense_on_even_odd_rays d hd
  refine ⟨n,?_⟩
  intro x y a b
  obtain ⟨R,hR,hkeep⟩ := hn x y a b
  refine ⟨R,hR,?_⟩
  intro t hl hnot
  let p : Pair :=
    ⟨((x+2*a*t:Nat):Int),((y+(2*b+1)*t:Nat):Int)⟩
  have hcert : excluded n p=true := by
    cases he : excluded n p with
    | false => exact False.elim (hnot (hkeep t he))
    | true => rfl
  have hm : Matches n (x+2*a*t) (y+(2*b+1)*t) p := by
    constructor <;> simp [Cong,p]
  exact source_excluded n p hcert _ _ hl hm

#print axioms source_checker_dense_on_even_odd_rays
end BB6.Agent21Duality
