import DyadicCheckerPermanentDensity
import DyadicRows

namespace BB6.Agent21Duality
open BB6.Agent21Dyadic
open BB6.Agent42ModularCone

/-- Uniform modular checker exclusion density one on EVERY horizontal
    section row, at one common bit precision independent of the row.
    This converts the inverse-word extinction theorem into an effective
    all-row certificate bound for the existing signed modular checker. -/
theorem checker_dense_on_all_rows (d : Nat) (hd : 0<d) :
    ∃ n : Nat, ∀ x : Nat, ∃ R : List Int,
      d*R.length≤2^n ∧ ∀ y : Nat,
        excluded n ⟨(x:Int),(y:Int)⟩=false →
        (y:Int)%BB6.Agent21Dyadic.P n∈R := by
  obtain ⟨n,hn⟩ := sparse_cover d hd
  refine ⟨n,?_⟩
  intro x
  obtain ⟨R,hR,hcover⟩ := hn (rowAffine x) (row_admissible x)
  refine ⟨R,hR,?_⟩
  intro y hno
  let s : Pair := ⟨(x:Int),(y:Int)⟩
  have hs : excluded n s=false := hno
  have ho : OpenAt (signedS s.x s.y) (signedZ s.x s.y) n := by
    by_cases h : OpenAt (signedS s.x s.y) (signedZ s.x s.y) n
    · exact h
    · have hcert := (excluded_open_duality n s).mpr h
      rw [hcert] at hs
      cases hs
  have hcoords := row_coords x y
  have ho' : OpenAt (mass (rowAffine x) (y:Int))
      (norm (rowAffine x) (y:Int)) n := by
    change OpenAt (S x y) (Z x y) n at ho
    rw [hcoords.1,hcoords.2] at ho
    exact ho
  exact hcover (y:Int) ho'

/-- All rows share one precision and one exception-cardinality bound.
    For any row and all larger precisions, every right counter outside
    that row's fixed exceptional residue set receives a positive
    executable checker certificate. It excludes genuine Machine C
    reachability wherever the source checker has its height guard. -/
theorem source_checker_permanent_dense_on_all_rows
    (d : Nat) (hd : 0<d) :
    ∃ n : Nat, ∀ x : Nat, ∃ R : List Int,
      d*R.length≤2^n ∧
      ∀ c y : Nat, n≤c →
        (y:Int)%BB6.Agent21Dyadic.P n∉R →
        excluded c ⟨(x:Int),(y:Int)⟩=true ∧
        (Large n y → ¬BB6.Agent3.CReach x y) := by
  obtain ⟨n,hn⟩ := checker_dense_on_all_rows d hd
  refine ⟨n,?_⟩
  intro x
  obtain ⟨R,hR,hkeep⟩ := hn x
  refine ⟨R,hR,?_⟩
  intro c y hnc hnot
  let s : Pair := ⟨(x:Int),(y:Int)⟩
  have hb : excluded n s=true := by
    cases he : excluded n s with
    | true => rfl
    | false => exact False.elim (hnot (hkeep y he))
  have hc : excluded c s=true := excluded_monotone_le n c hnc s hb
  refine ⟨hc,?_⟩
  intro hl
  have hm : Matches n x y s := by
    constructor <;> simp [Cong,s]
  exact source_excluded n s hb x y hl hm

#print axioms checker_dense_on_all_rows
#print axioms source_checker_permanent_dense_on_all_rows
end BB6.Agent21Duality
