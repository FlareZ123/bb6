import Lean
import Lean.Elab.Tactic.Omega
import HaltPreimageAudit

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace F011

/--
A potential for the F011 high-level state S(p,k,c).  The phase contribution
is 0 for p=false, 3 for p=true and k>0, and 2 for the exceptional p=true,k=0
states.
-/
def Potential (p : Bool) (k c : Nat) : Nat :=
  3 * (k / 3) + c + (if p then (if k = 0 then 2 else 3) else 0)

/-- The final tie-break coordinate: 1 exactly when k mod 3 is 2. -/
def ResidueTieBreak (k : Nat) : Nat :=
  if k % 3 = 2 then 1 else 0

/--
The lexicographic rank (Potential, floor(k/3), [k mod 3 = 2]).
This relation is written out explicitly to keep the certificate independent
of any library-specific lexicographic-order API.
-/
def RankAdvances (p p' : Bool) (k c k' c' : Nat) : Prop :=
  Potential p k c < Potential p' k' c' ∨
  (Potential p k c = Potential p' k' c' ∧ k / 3 < k' / 3) ∨
  (Potential p k c = Potential p' k' c' ∧ k / 3 = k' / 3 ∧
    ResidueTieBreak k < ResidueTieBreak k')

/--
Every defined transition strictly increases the lexicographic rank.
In particular, Potential is globally nondecreasing; its zero-increment
transitions either increase the quotient or move the residue tie-breaker
from 0 to 1.
-/
theorem rank_strict (p p' : Bool) (k c k' c' : Nat)
    (h : auditHighLevelNext (.S p k c) = some (.S p' k' c')) :
    RankAdvances p p' k c k' c' := by
  have hdiv : k = 3 * (k / 3) + k % 3 := by omega
  have hmod : k % 3 < 3 := Nat.mod_lt k (by decide)
  have hdiv' : k' = 3 * (k' / 3) + k' % 3 := by omega
  have hmod' : k' % 3 < 3 := Nat.mod_lt k' (by decide)
  cases p <;>
    simp [auditHighLevelNext, RankAdvances, Potential, ResidueTieBreak] at h ⊢ <;>
    split_ifs <;> simp_all <;> omega

/-- The first coordinate alone is a nondecreasing potential. -/
theorem potential_monotone (p p' : Bool) (k c k' c' : Nat)
    (h : auditHighLevelNext (.S p k c) = some (.S p' k' c')) :
    Potential p k c ≤ Potential p' k' c' := by
  rcases rank_strict p p' k c k' c' h with hlt | ⟨heq, hq⟩ | ⟨heq, hq, ht⟩ <;> omega

/-- There are no one-step fixed points of the copied high-level map. -/
theorem no_self_loop (p : Bool) (k c : Nat) :
    auditHighLevelNext (.S p k c) ≠ some (.S p k c) := by
  intro h
  have hr := rank_strict p p k c k c h
  simp [RankAdvances] at hr

end F011

#print axioms F011.rank_strict
#print axioms F011.potential_monotone
#print axioms F011.no_self_loop
