import DyadicStops
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

#print axioms source_low_sparse
#print axioms source_high_sparse
end BB6.Agent21Dyadic
