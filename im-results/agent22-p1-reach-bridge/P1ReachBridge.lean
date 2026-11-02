import P1Gate
import BlankCriterion

namespace BB6.Agent22P1

/-- Identity of Agent 1 and Agent 4's independently defined recursive P1 drains. -/
theorem G_eq (k c : Nat) :
    BB6.Agent1.G k c = BB6.HaltingFunnel.G k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases hlow : c < 2*k
    · rw [BB6.Agent1.G, BB6.HaltingFunnel.G]
      simp only [hlow, dite_true]
      exact ih (k-(c/2+1)) (by omega) (2*c+3)
    · by_cases hmid : c ≤ 2*k+1
      · simp [BB6.Agent1.G, BB6.HaltingFunnel.G, hlow, hmid]
      · simp [BB6.Agent1.G, BB6.HaltingFunnel.G, hlow, hmid]

/-- Identity of both complete P1 accelerated next-step functions. -/
theorem T_eq (a c : Nat) :
    BB6.Agent1.T a c = BB6.HaltingFunnel.T a c := by
  unfold BB6.Agent1.T BB6.HaltingFunnel.T
  simp only [G_eq]

/-- Any Agent4 finite trajectory from an Agent1-reachable state
remains reachable according to the actual Agent1 blank-root predicate. -/
theorem reach_transfer {a c b d : Nat}
    (h : BB6.HaltingFunnel.ReachT a c b d)
    (hr : BB6.Agent1.Reach a c) :
    BB6.Agent1.Reach b d := by
  induction h with
  | refl _ _ => exact hr
  | next a c b d e f ht htail ih =>
    have hab : BB6.Agent1.T a c = some (b,d) := by
      rw [T_eq]
      exact ht
    exact ih (BB6.Agent1.Reach.next a c b d hr hab)

/-- Actual source-linked P1 blank trajectory never reaches any n≡10(mod16)
critical halting gateway, with the exact unmodified Agent 4 ReachT relation. -/
theorem blank_reachT_excludes_10_mod16 (k : Nat) :
    ¬BB6.HaltingFunnel.ReachT 2 1 2
      (14*2^(16*k+10)-2*(16*k+10)-10) := by
  intro h
  exact BB6.Agent50P1.blank_no_critical_10_mod16 k
    (reach_transfer h BB6.Agent1.Reach.init)

#print axioms BB6.Agent22P1.G_eq
#print axioms BB6.Agent22P1.T_eq
#print axioms BB6.Agent22P1.blank_reachT_excludes_10_mod16

end BB6.Agent22P1
