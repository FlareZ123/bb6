import ARegular3AdicBridge
import First10AffineBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

/- Pending source-level wrapper. Compile after restoring the dependency closure
   in agent2-d-eighth-root.yml; do not cite this theorem as kernel-checked until
   that compile step succeeds. -/

namespace BB6.Agent4CryptidMacroReplay

open BB6.Agent2ARegular3AdicBridge
open BB6.DRegularSourceShift
open DRegular
open CryptidBoundary

/-- Original-source reachability of the first external halting-cylinder
    checkpoint, via the repository's authenticated DRegular source run.
    The duration is DRegular.accumulated 10; no equality with the external
    A_step2 macro runtime is asserted. -/
theorem cryptid_first10_source (k : Nat) :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated 10
          (BB6.DRegularSourceShift.inputLift cryptidStart 10 (3^98*k)))
        (ASection (cryptidCylinderC + 3^108*k) []))
      (ASection (cryptidCylinderC10 + 3^98*(8^10*k))
        (regularSuffix cryptidCheckpoint10)) := by
  have hc : DRegular.Canon cryptidStart := by
    norm_num [DRegular.Canon, cryptidStart, cryptidCylinderC]
  have hr : DRegular.run 10 cryptidStart = some cryptidCheckpoint10 :=
    _root_.cryptid_first10_base
  have h := synchronized_source cryptidStart cryptidCheckpoint10 10 (3^98*k) hc hr
  have hpow : 3^10 * 3^98 = 3^108 := by
    rw [← Nat.pow_add]
    norm_num
  have hInput :
      cryptidCylinderC + 3^10*(3^98*k) =
        cryptidCylinderC + 3^108*k := by
    calc
      _ = cryptidCylinderC + (3^10*3^98)*k := by rw [Nat.mul_assoc]
      _ = _ := by rw [hpow]
  have hOutput :
      cryptidCylinderC10 + 8^10*(3^98*k) =
        cryptidCylinderC10 + 3^98*(8^10*k) := by
    calc
      _ = cryptidCylinderC10 + (8^10*3^98)*k := by rw [Nat.mul_assoc]
      _ = cryptidCylinderC10 + (3^98*8^10)*k := by
        rw [Nat.mul_comm (8^10) (3^98)]
      _ = _ := by rw [← Nat.mul_assoc]
  simpa [cryptidStart, cryptidCheckpoint10, cryptidCylinderC,
    cryptidCylinderC10, regularSuffix, CryptidBoundary.oppairs,
    hInput, hOutput] using h

#print axioms cryptid_first10_source

end BB6.Agent4CryptidMacroReplay
