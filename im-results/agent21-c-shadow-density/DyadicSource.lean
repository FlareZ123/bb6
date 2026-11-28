import DyadicRays
import ModularConeSource

namespace BB6.Agent21Dyadic

-- The original-source parent theorem is definitionally the same interface.
theorem source_low_sparse (d : Nat) (hd : 0<d) :
    ∃ n, ∃ R : List Int, d*R.length≤2^n ∧ ∀ m y : Nat,
      n+2≤m → y+3*m+4=pow (2*m+3) → BB6.Agent3.CReach 1 y → (m:Int)%P n∈R :=
  low_sparse BB6.Agent3.CReach BB6.Agent42ModularCone.source_parent d hd

theorem source_high_sparse (d : Nat) (hd : 0<d) :
    ∃ n, ∀ m, ∃ R : List Int, d*R.length≤2^n ∧ ∀ j y : Nat,
      pow (n+2)≤j → y+j+3*m+4=pow (2*m+2)*(j+2) → BB6.Agent3.CReach (2*j+1) y → (j:Int)%P n∈R :=
  high_sparse BB6.Agent3.CReach BB6.Agent42ModularCone.source_parent d hd

/-- Authentic Machine C has uniformly sparse high-right reaches in every
    fixed-left row, at one precision independent of the row. -/
theorem source_all_rows_sparse (d : Nat) (hd : 0<d) :
    ∃ n, ∀ x, ∃ R : List Int, d*R.length≤2^n ∧ ∀ y : Nat,
      Large (n+2) y → BB6.Agent3.CReach x y → (y:Int)%P n∈R :=
  all_rows_sparse BB6.Agent3.CReach BB6.Agent42ModularCone.source_parent d hd

/-- Uniform dyadic sparsity for every authentic Machine C section ray with
    even left increment and odd right increment. -/
theorem source_ray_sparse (d : Nat) (hd : 0<d) :
    ∃ n, ∀ x y a b : Nat, ∃ R : List Int, d*R.length≤2^n ∧
      ∀ t : Nat, Large (n+2) (y+(2*b+1)*t) →
        BB6.Agent3.CReach (x+2*a*t) (y+(2*b+1)*t) → (t:Int)%P n∈R :=
  ray_sparse BB6.Agent3.CReach BB6.Agent42ModularCone.source_parent d hd

#print axioms source_ray_sparse
#print axioms source_all_rows_sparse
#print axioms source_low_sparse
#print axioms source_high_sparse
end BB6.Agent21Dyadic
