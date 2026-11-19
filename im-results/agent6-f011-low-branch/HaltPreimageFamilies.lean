import Lean
import Lean.Elab.Tactic.Omega
import HaltPreimageAudit

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace F011

/--
The two terminal states of the copied high-level map.  The parameter Q is
the quotient k / 3, so these are exactly the states with remainder 2 and
offset d = 1 (phase false) or d = 2 (phase true).
-/
def HaltTarget : AuditState → Prop
  | .S false k c => ∃ Q, k = 3 * Q + 2 ∧ c = Q + 1
  | .S true k c => ∃ Q, k = 3 * Q + 2 ∧ c = Q + 2

/--
The eight one-step predecessor families, in the coordinates
q = k / 3, r = k % 3, and c.

The first two families come from the low branch c < q.  The remaining six
come from the outer branch.  This predicate is intentionally written in
q,r,c coordinates so that the finite case analysis remains transparent.
-/
def HaltPreimageFamilies (p : Bool) (q r c : Nat) : Prop :=
  (p = false ∧ r = 1 ∧ c < q ∧ q = 5 * c + 5) ∨
  (p = true ∧ r = 1 ∧ c < q ∧ q = 5 * c + 4) ∨
  (p = false ∧ r = 0 ∧ ∃ m, 1 ≤ m ∧ q = 3 * m ∧ c = 7 * m + 1) ∨
  (p = false ∧ r = 1 ∧ ∃ m, q = 3 * m + 2 ∧ c = 7 * m + 7) ∨
  (p = false ∧ r = 2 ∧ ∃ m, q = 3 * m ∧ c = 7 * m + 7) ∨
  (p = true ∧ r = 0 ∧ ∃ m, q = 3 * m + 1 ∧ c = 7 * m + 8) ∨
  (p = true ∧ r = 1 ∧ ∃ m, q = 3 * m + 2 ∧ c = 7 * m + 8) ∨
  (p = true ∧ r = 2 ∧ ∃ m, q = 3 * m + 2 ∧ c = 7 * m + 14)

/-- The copied transition function returns none exactly on the two halt
states above. -/
theorem highLevelNext_none_iff (p : Bool) (k c : Nat) :
    auditHighLevelNext (.S p k c) = none ↔ HaltTarget (.S p k c) := by
  have hdiv : k = 3 * (k / 3) + k % 3 := by omega
  have hmod : k % 3 < 3 := Nat.mod_lt k (by decide)
  cases p <;>
    simp [auditHighLevelNext, HaltTarget] <;>
    split_ifs <;> simp_all <;> omega

/--
Exact one-step preimage classification for the copied high-level map:
a state maps directly to one of the two terminal states iff it belongs to
one of the eight affine families recorded in the dossier.
-/
theorem highLevelNext_halt_preimage_iff (p : Bool) (k c : Nat) :
    (∃ t, auditHighLevelNext (.S p k c) = some t ∧ HaltTarget t) ↔
      HaltPreimageFamilies p (k / 3) (k % 3) c := by
  have hdiv : k = 3 * (k / 3) + k % 3 := by omega
  have hmod : k % 3 < 3 := Nat.mod_lt k (by decide)
  cases p <;>
    simp [auditHighLevelNext, HaltTarget, HaltPreimageFamilies] <;>
    split_ifs <;> simp_all <;> omega

end F011

#print axioms F011.highLevelNext_none_iff
#print axioms F011.highLevelNext_halt_preimage_iff
