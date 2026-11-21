import BlankSixthExceptional
import First10AffineBridge

/-!
# Source-certified root section at the 13-step shadow

The sixth-exception proof already certifies a DRegular run of 4,494 transitions
from the fifth root reentry seed. This file extracts the prefix 4,484 steps,
which is the root section at section index 31,777 (the sixth exceptional
endpoint is index 31,787), and records its exact 3-adic residue.

**Compilation status:** uncompiled draft. The current invocation's local
Python/container tools fail with tool-level ClientError; do not treat the
declarations below as kernel-checked until the exact source closure compiles.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent4Root13Section

open CryptidBoundary BB6.BoundaryPadding

private def cylinderC : Nat :=
  1975700577069254261393123959451562008800234946348086

/-- The physical root's DRegular section ten regular returns before its
    sixth exceptional endpoint. -/
def root13Section : DRegular.L :=
  (DRegular.run 4484 BB6.Agent25SixthRoot.seed).getD ⟨0,0,0⟩

def root13P : Nat := (root13Section.a-cylinderC)/3^13

/-- One computational certificate shares the expensive 4,484-step reduction
    across all modular, shape, and endpoint obligations. -/
structure Root13Certificate : Prop where
  run_exact :
    DRegular.run 4484 BB6.Agent25SixthRoot.seed = some root13Section
  q_zero : root13Section.q = 0
  b_zero : root13Section.b = 0
  ge_C : root13Section.a ≥ cylinderC
  mod3pow14 :
    (root13Section.a-cylinderC) % 3^14 = 3^13
  p_mod2187 : root13P % 2187 = 205
  mod3pow20 : root13Section.a % 3^20 = 2863782241
  to_sixth_exception :
    DRegular.run 10 root13Section =
      some ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩

theorem root13Certificate : Root13Certificate := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem root13Section_exact :
    DRegular.run 4484 BB6.Agent25SixthRoot.seed = some root13Section :=
  root13Certificate.run_exact

theorem root13Section_shape :
    root13Section.q = 0 ∧ root13Section.b = 0 :=
  ⟨root13Certificate.q_zero, root13Certificate.b_zero⟩

theorem root13Section_mod3pow14 :
    (root13Section.a-cylinderC) % 3^14 = 3^13 :=
  root13Certificate.mod3pow14

theorem root13Section_ge_C :
    root13Section.a ≥ cylinderC :=
  root13Certificate.ge_C

theorem root13P_mod2187 : root13P % 2187 = 205 :=
  root13Certificate.p_mod2187

theorem root13Section_mod3pow20 :
    root13Section.a % 3^20 = 2863782241 :=
  root13Certificate.mod3pow20

theorem root13_to_sixth_exception :
    DRegular.run 10 root13Section =
      some ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩ :=
  root13Certificate.to_sixth_exception

/-- The root section is the 3^13-unary lift of the external cylinder start. -/
theorem root13Section_eq_lift :
    root13Section =
      BB6.DRegularShift.shiftNat cryptidStart (3^13*root13P) := by
  have hmod := root13Section_mod3pow14
  have hge := root13Section_ge_C
  apply DRegular.L.mk.inj
  constructor
  · simp [BB6.DRegularShift.shiftNat, cryptidStart, cryptidCylinderC,
      cylinderC, root13P]
    omega
  · exact root13Section_shape

/-- The first ten regular macro returns from the authentic root section are
    exactly the 3-adic affine lift of the external first-ten checkpoint.
    The suffix is unchanged by the lift. -/
theorem root13_first10_shift :
    DRegular.run 10 root13Section =
      (DRegular.run 10 cryptidStart).map
        (fun t => BB6.DRegularShift.shiftNat t
          (8^10*(3^3*root13P))) := by
  rw [root13Section_eq_lift]
  have hcanon : DRegular.Canon cryptidStart := by
    simp [DRegular.Canon, cryptidStart, cryptidCylinderC]
  have h := BB6.DRegularShift.run_shift 10 cryptidStart
    (3^3*root13P) hcanon
  have hpow : 3^10*(3^3*root13P) = 3^13*root13P := by
    calc
      3^10*(3^3*root13P) = (3^10*3^3)*root13P := by ac_rfl
      _ = 3^(10+3)*root13P := by rw [← Nat.pow_add]
      _ = 3^13*root13P := by congr 1; omega
  simpa [hpow] using h

theorem root13_first10_exact :
    DRegular.run 10 root13Section =
      some (BB6.DRegularShift.shiftNat cryptidCheckpoint10
        (8^10*(3^3*root13P))) := by
  rw [root13_first10_shift, cryptid_first10_base]
  rfl

/-- The section really is ten DRegular transitions before the already
    source-certified sixth exceptional endpoint. -/
theorem root13Section_original :
    ObsEq
      (run
        (BB6.Agent25FifthRoot.fifthReentryTime +
          DRegular.accumulated 4484 BB6.Agent25SixthRoot.seed)
        blank)
      (DRegularSource.sourceSection root13Section) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent25FifthRoot.fifthReentryTime
    4484 BB6.Agent25SixthRoot.seed root13Section
  · constructor
    · change 64*BB6.Agent25FifthRoot.t5+27 ≥ 2
      omega
    · left
      change 1 ≠ 0
      omega
  · exact root13Section_exact
  · exact BB6.Agent25FifthRoot.fifthReentry_original

#print axioms root13Certificate
#print axioms root13Section_mod3pow14
#print axioms root13P_mod2187
#print axioms root13_first10_exact
#print axioms root13_to_sixth_exception
#print axioms root13Section_original

end BB6.Agent4Root13Section
