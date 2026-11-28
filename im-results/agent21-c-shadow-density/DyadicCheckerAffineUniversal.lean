import DyadicCheckerPermanentRows

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

/-- Every pair of arbitrary signed mass/normalized-numerator coordinates
    has an exact corresponding signed two-counter representative. This
    algebraic inverse works also for negative counters. -/
def pairOfMassNorm (s z:Int):Pair :=
  ⟨-2*z-2-parity s,(2*z+2+parity s-s)/2⟩

theorem pairOfMassNorm_coords (s z:Int):
    signedS (pairOfMassNorm s z).x (pairOfMassNorm s z).y=s ∧
    signedZ (pairOfMassNorm s z).x (pairOfMassNorm s z).y=z := by
  have he:(2*z+2+parity s-s)%2=0:=by
    unfold parity
    omega
  have hy:2*((2*z+2+parity s-s)/2)=2*z+2+parity s-s:=by omega
  have hmass:signedS (pairOfMassNorm s z).x (pairOfMassNorm s z).y=s:=by
    unfold signedS pairOfMassNorm
    dsimp
    omega
  constructor
  · exact hmass
  · unfold signedZ
    rw [hmass]
    unfold pairOfMassNorm
    dsimp
    omega

/-- Strongest source-independent form of checker density: a single
    universal precision n excludes a fraction >=1-1/d of EVERY
    admissible signed affine family, and exclusion persists at ALL
    later checker precisions c>=n. Unlike ray/row corollaries this
    permits arbitrary signed offsets and increments; admissibility
    is precisely 'mass slope even, normalized-numerator plus
    half-mass slope odd'. -/
theorem checker_permanent_dense_all_admissible_affines
    (d:Nat) (hd:0<d):
    ∃ n:Nat,∀ a:Affine, Admissible a→∃ R:List Int,
      d*R.length≤2^n ∧
      ∀ c:Nat,∀ t:Int, n≤c→t%BB6.Agent21Dyadic.P n∉R→
        excluded c (pairOfMassNorm (mass a t) (norm a t))=true := by
  obtain ⟨n,hn⟩ := sparse_cover d hd
  refine ⟨n,?_⟩
  intro a ha
  obtain ⟨R,hR,hcover⟩ := hn a ha
  refine ⟨R,hR,?_⟩
  intro c t hnc hnot
  let p:Pair:=pairOfMassNorm (mass a t) (norm a t)
  have hbase:excluded n p=true:=by
    cases he:excluded n p with
    | true=>rfl
    | false=>
       have ho:OpenAt (signedS p.x p.y) (signedZ p.x p.y) n := by
         by_cases h:OpenAt (signedS p.x p.y) (signedZ p.x p.y) n
         · exact h
         · have hcert := (excluded_open_duality n p).mpr h
           rw [he] at hcert
           cases hcert
       have hcoords:=pairOfMassNorm_coords (mass a t) (norm a t)
       have ho':OpenAt (mass a t) (norm a t) n:=by
         rw [hcoords.1,hcoords.2] at ho
         exact ho
       exact False.elim (hnot (hcover t ho'))
  exact excluded_monotone_le n c hnc p hbase

#print axioms pairOfMassNorm_coords
#print axioms checker_permanent_dense_all_admissible_affines
end BB6.Agent21Duality
