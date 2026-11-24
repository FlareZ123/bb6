import NearPowerAffineFatal

namespace BB6.Agent41NearPower
open BB6.Agent41FatalInverse BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- The fatal state with an arbitrary positive even leading coefficient. -/
def generalFamilyAffine (coeff R : Nat) (off : Int) : Aff :=
  ⟨(coeff : Int) * (3 : Int)^R, 0, off⟩

structure CertifiedGeneralFamily where
  coeff : Nat
  R : Nat
  off : Int
  cert : SymCert
  accepted : symCheck (affineFatal (generalFamilyAffine coeff R off)) cert = true

def generalFamilyExponent (f : CertifiedGeneralFamily) (n : Nat) : Nat :=
  ((generalFamilyAffine f.coeff f.R f.off).eval n).toNat

/-- Every member of every accepted generalized family is absent from the
entire authenticated blank-origin orbit, at every return index. -/
theorem general_family_excluded (f : CertifiedGeneralFamily) (n i : Nat) :
    run i ≠ some (.D (targetX (generalFamilyExponent f n - 1))
                     (targetY (generalFamilyExponent f n - 1))) := by
  simpa [generalFamilyExponent] using
    (affineFatal_excluded (generalFamilyAffine f.coeff f.R f.off)
      f.cert f.accepted n i)

#print axioms general_family_excluded
end BB6.Agent41NearPower
