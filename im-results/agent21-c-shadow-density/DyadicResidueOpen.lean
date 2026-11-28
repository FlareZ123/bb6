import DyadicSignedPeriod
import ModularCone

namespace BB6.Agent21Dyadic

/-- At any positive bit precision, normalization to canonical signed
    residues is mathematically *invisible* to the full completed/pending
    inverse-word feasibility language. -/
theorem signed_open_residue (b : Nat)
    (s : BB6.Agent42ModularCone.Pair) :
    OpenAt
      (signedS (BB6.Agent42ModularCone.residue b s).x
        (BB6.Agent42ModularCone.residue b s).y)
      (signedZ (BB6.Agent42ModularCone.residue b s).x
        (BB6.Agent42ModularCone.residue b s).y) b ↔
    OpenAt (signedS s.x s.y) (signedZ s.x s.y) b := by
  cases b with
  | zero =>
      constructor <;> intro _ <;> exact open_zero _ _
  | succ n =>
      let d : Int := P (n+1)
      let u : Int := -(s.x/d)
      let v : Int := -(s.y/d)
      have hp : BB6.Agent42ModularCone.I (n+1)=d := by
        dsimp [d,P,BB6.Agent42ModularCone.I,BB6.Agent42ModularCone.P]
        rfl
      have hx : (BB6.Agent42ModularCone.residue (n+1) s).x =
          s.x+d*u := by
        simp only [BB6.Agent42ModularCone.residue,hp]
        change s.x%d=s.x+d*(-(s.x/d))
        have he := Int.emod_add_mul_ediv s.x d
        rw [Int.mul_neg]
        omega
      have hy : (BB6.Agent42ModularCone.residue (n+1) s).y =
          s.y+d*v := by
        simp only [BB6.Agent42ModularCone.residue,hp]
        change s.y%d=s.y+d*(-(s.y/d))
        have he := Int.emod_add_mul_ediv s.y d
        rw [Int.mul_neg]
        omega
      rw [hx,hy]
      exact signed_open_period s.x s.y u v n

#print axioms signed_open_residue
end BB6.Agent21Dyadic
