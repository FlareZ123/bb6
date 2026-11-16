import Lean.Elab.Tactic.Omega
import BlankThirtySeventhToThirtyEighthRejoin
import Seed31FirstStopCertificate

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37Seed39Probe

open DRegular

def seed39 : DRegular.L :=
  BB6.Agent37ThirtySeventhToThirtyEighthRejoin.seed39

def firstExceptionFromSeed39 : Nat × DRegular.L :=
  BB6.Agent2ThirtyFirstProbe.firstStopBlocks 2000 0 seed39

/-- Diagnostic projection: if the count is below 1,024,000, the
    second component is the first undefined successor in DRegular. -/
#eval
  let (n, s) := firstExceptionFromSeed39
  (n, s.a % 59049, s.q, s.b, (DRegular.next s).isNone)

/-- The reusable block-search soundness theorem turns any bounded
    probe result into an exact first-stop theorem for this seed. -/
theorem firstExceptionFromSeed39_sound
    (hbound : firstExceptionFromSeed39.1 < 1024000) :
    DRegular.run firstExceptionFromSeed39.1 seed39 =
        some firstExceptionFromSeed39.2 ∧
      DRegular.next firstExceptionFromSeed39.2 = none := by
  obtain ⟨k, hcount, hboundK, hrun, hstop⟩ :=
    BB6.Agent2ThirtyFirstCertificate.firstStopBlocks_sound
      2000 0 seed39
      BB6.Agent37ThirtySeventhToThirtyEighthRejoin.seed39_canon
  have hk : k < 1024000 := by
    simpa [firstExceptionFromSeed39, hcount] using hbound
  constructor
  · simpa [firstExceptionFromSeed39, hcount] using hrun
  · simpa [firstExceptionFromSeed39, hcount] using hstop (by omega)

#print axioms firstExceptionFromSeed39_sound

end BB6.Agent37Seed39Probe
