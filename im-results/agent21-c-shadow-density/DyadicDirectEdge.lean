import DyadicSignedOpen
import ModularCone

namespace BB6.Agent21Dyadic

/-- Signed direct inverse branch is an exact inverse-word prefix in
    *both* normalized coordinates. The source cone operates over
    signed residues, so nonnegative predecessor assumptions are wrong
    here and deliberately absent. -/
theorem signed_direct_edge (x y : Int) (hy : y%2=0) :
    let a := x+y-2
    let k := (y-2)/2
    signedS a k=signedS x y+shift 1 ∧
      P 1*signedZ a k=signedZ x y+offset (signedS x y) 1 := by
  let a : Int := x+y-2
  let k : Int := (y-2)/2
  have hk : 2*k=y-2 := by dsimp [k]; omega
  have hs : signedS a k=signedS x y+shift 1 := by
    dsimp [signedS,shift,a]
    omega
  have hpar : (1:Int)%2=(y+1)%2 := by omega
  have hp : parity (signedS a k)=(x+y)%2 := by
    rw [hs]
    exact signed_parity_cost x y 1 hpar
  have hfirst : signedZ x y+offset (signedS x y) 1 =
      -(x+y+(x+y)%2) := by
    rw [signed_one_numer,signed_parity_cost x y 1 hpar]
    omega
  have hz := signed_twice_Z a k
  rw [hp] at hz
  refine ⟨hs,?_⟩
  change 2*signedZ a k=signedZ x y+offset (signedS x y) 1
  rw [hfirst]
  dsimp [a] at hz ⊢
  omega

theorem direct_edge_source_pair (s : BB6.Agent42ModularCone.Pair)
    (hy : s.y%2=0) :
    signedS (BB6.Agent42ModularCone.direct s).x
        (BB6.Agent42ModularCone.direct s).y =
      signedS s.x s.y+shift 1 ∧
    P 1*signedZ (BB6.Agent42ModularCone.direct s).x
        (BB6.Agent42ModularCone.direct s).y =
      signedZ s.x s.y+offset (signedS s.x s.y) 1 := by
  simpa [BB6.Agent42ModularCone.direct] using signed_direct_edge s.x s.y hy

#print axioms direct_edge_source_pair
end BB6.Agent21Dyadic
