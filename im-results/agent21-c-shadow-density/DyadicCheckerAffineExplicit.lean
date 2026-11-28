import DyadicCheckerAffineUniversal
import DyadicExplicitCover

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

/-- The universal all-signed-affine checker density theorem has an
    EXPLICIT computable precision, namely the uniform finite-tree
    extinction depth sparseCertificateDepth d. The entire checker
    certificate remains valid at each later precision c. This theorem
    is constructive in d and the affine input: the exceptional list
    is built by the finite witness tree in sparse_cover_explicit. -/
theorem checker_permanent_dense_all_affines_explicit
    (d:Nat) (hd:0<d) (a:Affine) (ha:Admissible a):
    ∃ R:List Int,
      d*R.length≤2^(sparseCertificateDepth d) ∧
      ∀ c:Nat,∀ t:Int,
        sparseCertificateDepth d≤c →
        t%BB6.Agent21Dyadic.P (sparseCertificateDepth d)∉R →
        excluded c (pairOfMassNorm (mass a t) (norm a t))=true := by
  obtain ⟨R,hR,hcover⟩ := sparse_cover_explicit d hd a ha
  refine ⟨R,hR,?_⟩
  intro c t hnc hnot
  let n:=sparseCertificateDepth d
  let p:Pair:=pairOfMassNorm (mass a t) (norm a t)
  have hbase:excluded n p=true:=by
    cases he:excluded n p with
    | true=>rfl
    | false=>
      have ho:OpenAt (signedS p.x p.y) (signedZ p.x p.y) n := by
        by_cases h:OpenAt (signedS p.x p.y) (signedZ p.x p.y) n
        · exact h
        · have hcert:excluded n p=true :=
            (excluded_open_duality n p).mpr h
          rw [he] at hcert
          cases hcert
      have hcoords:=pairOfMassNorm_coords (mass a t) (norm a t)
      have ho':OpenAt (mass a t) (norm a t) n:=by
        rw [hcoords.1,hcoords.2] at ho
        exact ho
      exact False.elim (hnot (hcover t ho'))
  exact excluded_monotone_le n c hnc p hbase

#print axioms checker_permanent_dense_all_affines_explicit
end BB6.Agent21Duality
