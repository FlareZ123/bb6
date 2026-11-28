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

/-- The signed plane-to-mass/normal coordinate map is bijective. -/
theorem pairOfMassNorm_left (x y:Int):
    pairOfMassNorm (signedS x y) (signedZ x y)=⟨x,y⟩ := by
  have hz : 2*signedZ x y=-x-2-parity (signedS x y) :=
    signed_twice_Z x y
  have hx : (pairOfMassNorm (signedS x y) (signedZ x y)).x=x := by
    dsimp [pairOfMassNorm]
    omega
  have hy : (pairOfMassNorm (signedS x y) (signedZ x y)).y=y := by
    dsimp [pairOfMassNorm]
    unfold signedS at *
    omega
  cases h : pairOfMassNorm (signedS x y) (signedZ x y) with
  | mk xx yy =>
      simp only [h] at hx hy
      cases hx
      cases hy
      rfl

/-- Every admissible mass/normal affine line maps exactly to a line in
    signed two-counter coordinates, whose left increment is even. -/
theorem pairOfMassNorm_affine (a:Affine) (ha:a.sigma%2=0) (t:Int):
    pairOfMassNorm (mass a t) (norm a t) =
      ⟨(pairOfMassNorm a.s a.z).x+(-2*a.lam)*t,
        (pairOfMassNorm a.s a.z).y+(a.lam-a.sigma/2)*t⟩ := by
  have hsigma : a.sigma=2*(a.sigma/2) := by omega
  have heven : a.sigma*t=2*((a.sigma/2)*t) := by
    calc
      a.sigma*t=(2*(a.sigma/2))*t :=
        congrArg (fun v:Int => v*t) hsigma
      _=2*((a.sigma/2)*t) := by rw [Int.mul_assoc]
  have hmass : mass a t=a.s+2*((a.sigma/2)*t) := by
    unfold mass
    rw [heven]
  have hpar : parity (mass a t)=parity a.s := by
    rw [hmass]
    unfold parity
    omega
  have hx : (pairOfMassNorm (mass a t) (norm a t)).x=
      (pairOfMassNorm a.s a.z).x+(-2*a.lam)*t := by
    change -2*(norm a t)-2-parity (mass a t) =
      -2*a.z-2-parity a.s+(-2*a.lam)*t
    rw [hpar]
    unfold norm
    rw [Int.mul_add]
    rw [Int.mul_assoc]
    omega
  have hy : (pairOfMassNorm (mass a t) (norm a t)).y=
      (pairOfMassNorm a.s a.z).y+(a.lam-a.sigma/2)*t := by
    change (2*(norm a t)+2+parity (mass a t)-(mass a t))/2 =
      (2*a.z+2+parity a.s-a.s)/2+(a.lam-a.sigma/2)*t
    rw [hpar]
    rw [hmass]
    unfold norm
    have heq :
        2*(a.z+a.lam*t)+2+parity a.s-(a.s+(2*((a.sigma/2)*t))) =
        (2*a.z+2+parity a.s-a.s)+2*((a.lam-a.sigma/2)*t) := by
      rw [Int.mul_add,Int.sub_mul,Int.mul_sub]
      omega
    rw [heq]
    have hm : (2*a.z+2+parity a.s-a.s)%2=0 := by
      unfold parity
      omega
    omega
  cases h : pairOfMassNorm (mass a t) (norm a t) with
  | mk xx yy =>
      simp only [h] at hx hy
      cases hx
      cases hy
      rfl

/-- The right-counter increment of every admissible signed affine line
    is odd; the normalized affine condition is exactly the geometric
    odd-direction condition. -/
theorem admissible_signed_slope_odd (a:Affine) (ha:Admissible a):
    (a.lam-a.sigma/2)%2=1 := by
  rcases ha with ⟨he,ho⟩
  have hsigma : a.sigma=2*(a.sigma/2) := by omega
  omega

#print axioms pairOfMassNorm_left
#print axioms pairOfMassNorm_affine
#print axioms admissible_signed_slope_odd

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
