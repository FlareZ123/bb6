import BlankSixthExceptional

/-!
# Source-certified root section at the 13-step shadow

The sixth-exception proof already certifies a DRegular run of 4,494 transitions
from the fifth root reentry seed. This file extracts the prefix 4,484 steps,
which is the root section at section index 31,777 (the sixth exceptional
endpoint is index 31,787), and records its exact 3-adic residue.

**Compilation status:** uncompiled draft. The current invocation's local
Python/container tools fail with ClientError; do not treat the declarations
below as kernel-checked until the exact source closure compiles.
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

theorem root13Section_exact :
    DRegular.run 4484 BB6.Agent25SixthRoot.seed = some root13Section := by
  decide

theorem root13Section_shape :
    root13Section.q = 0 ∧ root13Section.b = 0 := by
  decide

theorem root13Section_mod3pow14 :
    (root13Section.a - cylinderC) % 3^14 = 3^13 := by
  decide

theorem root13Section_ge_C :
    root13Section.a ≥ cylinderC := by
  decide

def root13P : Nat := (root13Section.a-cylinderC)/3^13

theorem root13P_mod2187 : root13P % 2187 = 205 := by
  decide

theorem root13Section_mod3pow20 :
    root13Section.a % 3^20 = 2863782241 := by
  decide

/-- The section really is ten DRegular transitions before the already
    source-certified sixth exceptional endpoint. -/
theorem root13_to_sixth_exception :
    DRegular.run 10 root13Section =
      some ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩ := by
  decide

/-- The blank-root orbit physically reaches this section. This reuses the
    existing fifth-reentry source theorem and the same original-source
    DRegular extension theorem as the sixth-exception proof. -/
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

#print axioms root13Section_exact
#print axioms root13Section_mod3pow14
#print axioms root13P_mod2187
#print axioms root13_to_sixth_exception
#print axioms root13Section_original

end BB6.Agent4Root13Section
