import DyadicStops
namespace BB6.Agent21Dyadic

/-- With x fixed, exact signed coordinates are affine in y. -/
def rowAffine (x : Nat) : Affine := ⟨-(x:Int),-2,Z x 0,0⟩

theorem row_admissible (x : Nat) : Admissible (rowAffine x) := by
  change (-2:Int)%2=0 ∧ (0+(-2:Int)/2)%2=1
  decide

theorem row_coords (x y : Nat) : S x y=mass (rowAffine x) y ∧ Z x y=norm (rowAffine x) y := by
  constructor
  · simp [S,mass,rowAffine]; omega
  · unfold norm rowAffine; dsimp; unfold Z S parity
    omega

/-- At a fixed height threshold, the full large-right parent law forces a
    uniformly sparse set of reachable right-counter residues in every row.
    The same precision and threshold work for all left counters. -/
theorem all_rows_sparse (reach : Nat→Nat→Prop) (parent : ParentLaw reach)
    (d : Nat) (hd : 0<d) :
    ∃ n, ∀ x, ∃ R : List Int, d*R.length≤2^n ∧ ∀ y : Nat,
      Large (n+2) y → reach x y → (y:Int)%P n∈R := by
  obtain ⟨n,hn⟩ := sparse_cover d hd
  refine ⟨n,?_⟩
  intro x
  obtain ⟨R,hR,hcover⟩ := hn (rowAffine x) (row_admissible x)
  refine ⟨R,hR,?_⟩
  intro y hy hr
  have ho := reach_open reach parent n x y hy hr
  obtain ⟨hs,hz⟩ := row_coords x y
  rw [hs,hz] at ho
  exact hcover _ ho

#print axioms all_rows_sparse
end BB6.Agent21Dyadic
