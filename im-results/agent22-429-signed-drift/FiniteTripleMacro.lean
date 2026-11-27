import PeriodicMacroTransfer
import FiniteTripleRigidity

namespace PeriodicMacro

/-- Three actual repeats of the same exact typed macro word, whose paired
    inputs remain in the safe half-rank region, force an integer-affine
    first-coordinate slope when the period denominator is large enough. -/
theorem triple_word_slope
    (xs : List Letter)
    (u0 u1 u2 u3 r0 r1 r2 r3 : Nat)
    (w0 : Walk xs u0 r0 u1 r1)
    (w1 : Walk xs u1 r1 u2 r2)
    (w2 : Walk xs u2 r2 u3 r3)
    (h0 : 3*u0 ≤ r0) (h1 : 3*u1 ≤ r1) (h2 : 3*u2 ≤ r2)
    (hbig : 2*((r0 + 2*T xs)/3) < M xs) :
    (u0:Int)+(u2:Int)=2*(u1:Int) ∧
      ((M xs:Int)-1)*((u1:Int)-(u0:Int))=((A xs*T xs):Int) := by
  obtain ⟨hm0,hr1⟩ := transfer w0
  obtain ⟨hm1,hr2⟩ := transfer w1
  obtain ⟨hm2,_⟩ := transfer w2
  let H : Nat := (r0 + 2*T xs)/3
  have hr2eq : r2 = r0 + 2*T xs := by
    rw [hr2,hr1]
    omega
  have hb0 : u0 ≤ H := by
    dsimp [H]
    omega
  have hb1 : u1 ≤ H := by
    dsimp [H]
    rw [hr1] at h1
    omega
  have hb2 : u2 ≤ H := by
    dsimp [H]
    rw [hr2eq] at h2
    omega
  have hform1 : M xs*u2 = u1 + (A xs*T xs) + (A xs*r0+B xs) := by
    rw [hr1] at hm1
    grind
  have hform2 : M xs*u3 = u2 + 2*(A xs*T xs) + (A xs*r0+B xs) := by
    rw [hr2eq] at hm2
    grind
  have hret := PeriodicTriple.three_periods_force_affine
    (M xs) H u0 u1 u2 u3 (A xs*T xs) (A xs*r0+B xs)
    hbig hb0 hb1 hb2 (by grind : M xs*u1 = u0+(A xs*r0+B xs))
    hform1 hform2
  exact hret

#print axioms triple_word_slope
end PeriodicMacro
