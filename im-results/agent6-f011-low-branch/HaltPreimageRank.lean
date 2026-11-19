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

/-- Lexicographic order on the pair (Potential, ResidueTieBreak). -/
def LexLt (a b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

def Rank (s : AuditState) : Nat × Nat :=
  match s with
  | .S p k c => (Potential p k c, ResidueTieBreak k)

theorem lexLt_trans {a b c : Nat × Nat}
    (hab : LexLt a b) (hbc : LexLt b c) : LexLt a c := by
  rcases hab with hab | ⟨habEq, habSnd⟩
  · rcases hbc with hbc | ⟨hbcEq, _⟩
    · exact Or.inl (Nat.lt_trans hab hbc)
    · exact Or.inl (by simpa [hbcEq] using hab)
  · rcases hbc with hbc | ⟨hbcEq, hbcSnd⟩
    · exact Or.inl (by simpa [habEq] using hbc)
    · exact Or.inr ⟨habEq.trans hbcEq, Nat.lt_trans habSnd hbcSnd⟩

/--
Every defined transition strictly increases (W, 1_{k mod 3 = 2}).
Thus W is nondecreasing, and every zero-W transition moves the tie-break
coordinate from 0 to 1.
-/
theorem rank_strict (p p' : Bool) (k c k' c' : Nat)
    (h : auditHighLevelNext (.S p k c) = some (.S p' k' c')) :
    LexLt (Rank (.S p k c)) (Rank (.S p' k' c')) := by
  have hdiv : k = 3 * (k / 3) + k % 3 := by omega
  have hmod : k % 3 < 3 := Nat.mod_lt k (by decide)
  have hdiv' : k' = 3 * (k' / 3) + k' % 3 := by omega
  have hmod' : k' % 3 < 3 := Nat.mod_lt k' (by decide)
  cases p <;>
    simp [auditHighLevelNext, Rank, LexLt, Potential, ResidueTieBreak] at h ⊢ <;>
    split_ifs <;> simp_all <;> omega

/-- The first coordinate alone is a nondecreasing potential. -/
theorem potential_monotone (p p' : Bool) (k c k' c' : Nat)
    (h : auditHighLevelNext (.S p k c) = some (.S p' k' c')) :
    Potential p k c ≤ Potential p' k' c' := by
  have hr := rank_strict p p' k c k' c' h
  rcases hr with hlt | ⟨heq, htie⟩ <;> omega

/-- Every defined transition out of residue class 2 strictly raises W. -/
theorem potential_strict_from_r2 (p p' : Bool) (k c k' c' : Nat)
    (hr : k % 3 = 2)
    (h : auditHighLevelNext (.S p k c) = some (.S p' k' c')) :
    Potential p k c < Potential p' k' c' := by
  have hdiv : k = 3 * (k / 3) + k % 3 := by omega
  have hmod : k % 3 < 3 := Nat.mod_lt k (by decide)
  have hdiv' : k' = 3 * (k' / 3) + k' % 3 := by omega
  have hmod' : k' % 3 < 3 := Nat.mod_lt k' (by decide)
  cases p <;>
    simp [auditHighLevelNext, Potential] at h ⊢ <;>
    split_ifs <;> simp_all <;> omega

/--
Across any two consecutive defined transitions, W rises by at least one.
If the first transition leaves W unchanged, rank_strict forces its output
to have residue 2, from which the next transition strictly raises W.
-/
theorem potential_two_step_growth
    (p p' p'' : Bool) (k c k' c' k'' c'' : Nat)
    (h1 : auditHighLevelNext (.S p k c) = some (.S p' k' c'))
    (h2 : auditHighLevelNext (.S p' k' c') = some (.S p'' k'' c'')) :
    Potential p k c + 1 ≤ Potential p'' k'' c'' := by
  have hmono1 := potential_monotone p p' k c k' c' h1
  have hmono2 := potential_monotone p' p'' k' c' k'' c'' h2
  by_cases heq : Potential p k c = Potential p' k' c'
  · have hrank := rank_strict p p' k c k' c' h1
    have htie : ResidueTieBreak k < ResidueTieBreak k' := by
      rcases hrank with hlt | ⟨_, htie⟩
      · omega
      · exact htie
    have hr2 : k' % 3 = 2 := by
      unfold ResidueTieBreak at htie
      split_ifs at htie <;> omega
    have hstrict := potential_strict_from_r2 p' p'' k' c' k'' c'' hr2 h2
    omega
  · have hlt : Potential p k c < Potential p' k' c' := by omega
    omega

/--
The only zero-W transitions are: (p=false,r=0,q=3m,m>=1,d>=1), (p=false,r=1,q=3m+2,d>=2), (p=true,q=0,r=0), and (p=true,r=1,q=3m+2,d>=2). All land at r'=2; every defined transition from r=2 strictly raises W.
-/
/-- Iteration stops if a transition returns none. -/
def iterateHighLevel : Nat → AuditState → Option AuditState
  | 0, s => some s
  | n + 1, s => (auditHighLevelNext s).bind (iterateHighLevel n)

theorem iterateHighLevel_rank_strict :
    ∀ n s t, 0 < n → iterateHighLevel n s = some t → LexLt (Rank s) (Rank t) := by
  intro n
  induction n with
  | zero =>
    intro s t hn hrun
    omega
  | succ n ih =>
    intro s t hn hrun
    cases s with
    | S p k c =>
      simp only [iterateHighLevel] at hrun
      cases hstep : auditHighLevelNext (.S p k c) with
      | none =>
        simp [hstep] at hrun
      | some s1 =>
        simp [hstep] at hrun
        have hfirst : LexLt (Rank (.S p k c)) (Rank s1) := by
          cases s1 with
          | S p' k' c' => exact rank_strict p p' k c k' c' hstep
        by_cases hn0 : n = 0
        · subst n
          simp [iterateHighLevel] at hrun
          cases hrun
          exact hfirst
        · exact lexLt_trans hfirst (ih s1 t (by omega) hrun)

/-- No positive-length defined orbit can return to its starting state. -/
theorem no_positive_cycle (n : Nat) (s : AuditState) (hn : 0 < n) :
    iterateHighLevel n s ≠ some s := by
  intro h
  have hr := iterateHighLevel_rank_strict n s s hn h
  cases s with
  | S p k c =>
    simp [LexLt, Rank] at hr

end F011

#print axioms F011.rank_strict
#print axioms F011.potential_monotone
#print axioms F011.potential_strict_from_r2
#print axioms F011.potential_two_step_growth
#print axioms F011.iterateHighLevel_rank_strict
#print axioms F011.no_positive_cycle
