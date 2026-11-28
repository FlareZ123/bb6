import DyadicCheckerAffineUniversal

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

/-- All-affine density-one certificates are stable in both dimensions:
    outside a fixed sparse set of parameter residues, the entire
    2^n-by-2^n congruence cylinder around the signed state is excluded
    by the *same executable checker*, at every later precision c>=n.
    This is stronger than certification of just the original affine
    trajectory, and is the precise 2-adic neighbourhood interpretation. -/
theorem checker_permanent_dense_affine_tubes (d:Nat) (hd:0<d):
    ∃ n:Nat,∀a:Affine, Admissible a→∃R:List Int,
      d*R.length≤2^n ∧
      ∀ c:Nat,∀t:Int,∀q:Pair,
        n≤c →
        t%BB6.Agent21Dyadic.P n∉R →
        Cong n (pairOfMassNorm (mass a t) (norm a t)).x q.x →
        Cong n (pairOfMassNorm (mass a t) (norm a t)).y q.y →
        excluded c q=true := by
  obtain ⟨n,hn⟩ := checker_permanent_dense_all_admissible_affines d hd
  refine ⟨n,?_⟩
  intro a ha
  obtain ⟨R,hR,hkeep⟩ := hn a ha
  refine ⟨R,hR,?_⟩
  intro c t q hnc hnot hx hy
  let p:Pair:=pairOfMassNorm (mass a t) (norm a t)
  have hbase:excluded n p=true :=
    hkeep n t (Nat.le_refl n) hnot
  exact excluded_monotone_congr n c hnc p q hx hy hbase

#print axioms checker_permanent_dense_affine_tubes
end BB6.Agent21Duality
