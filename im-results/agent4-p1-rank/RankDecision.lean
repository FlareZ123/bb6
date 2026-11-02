import Rank

namespace BB6.P1Rank
open BB6.Agent1

/-- The deterministic accelerated blank-entry trace, stopping on none. -/
def run : Nat → Option (Nat × Nat)
  | 0 => some (2,1)
  | n+1 => (run n).bind (fun p => T p.1 p.2)

/-- Every reachable target is attained within its rank-dependent horizon. -/
theorem reach_has_run (a c:Nat) (h:Reach a c) :
    ∃ n, n+3≤a+c ∧ run n=some (a,c) := by
  induction h with
  | init => exact ⟨0,by decide,by rfl⟩
  | next a c b d hp ht ih =>
    obtain ⟨n,hrank,heq⟩ := ih
    have hinc := T_sum_growth a c b d ht
    refine ⟨n+1,by omega,?_⟩
    simp [run,heq,ht]

/-- Soundness of the executable trajectory against the original Reach. -/
theorem run_reachable (n:Nat) (a c:Nat) (h:run n=some (a,c)) :
    Reach a c := by
  induction n generalizing a c with
  | zero =>
    change some (2,1) = some (a,c) at h
    have hp : (2,1) = (a,c) := Option.some.inj h
    have ha : a=2 := (Prod.mk.inj hp).1.symm
    have hc : c=1 := (Prod.mk.inj hp).2.symm
    subst a
    subst c
    exact Reach.init
  | succ n ih =>
    cases hv : run n with
    | none =>
      simp [run,hv] at h
    | some pair =>
      rcases pair with ⟨b,d⟩
      have hh : T b d = some (a,c) := by simpa [run,hv] using h
      exact Reach.next b d a c (ih b d hv) hh

theorem reach_iff_bounded_run (a c:Nat) :
    Reach a c ↔ ∃ n, n+3≤a+c ∧ run n=some (a,c) := by
  constructor
  · exact reach_has_run a c
  · rintro ⟨n,_,h⟩
    exact run_reachable n a c h

/-- Each finite accelerated trajectory increases additive rank by at least its length. -/
theorem iter_rank_growth (n a c b d : Nat) (h:Iter n a c b d) :
    n+a+c ≤ b+d := by
  induction h with
  | refl a c => omega
  | step n a c b d e f hp ht ih =>
      have hs := T_sum_growth b d e f ht
      omega

/-- No positive-length accelerated trajectory can revisit its starting state. -/
theorem no_positive_cycle (n a c : Nat) : ¬Iter (n+1) a c a c := by
  intro h
  have hr := iter_rank_growth (n+1) a c a c h
  omega

private theorem finite_iff (a c : Nat) :
    (∃ n : Fin (a+c+1), run n.val=some (a,c)) ↔ Reach a c := by
  constructor
  · rintro ⟨n,hn⟩
    exact run_reachable n.val a c hn
  · intro hr
    obtain ⟨n,hbound,hn⟩ := reach_has_run a c hr
    exact ⟨⟨n,by omega⟩,hn⟩

/-- Computable decision procedure for the original blank-entry Reach predicate,
    for any *fixed* target. No uniform bound on halting-target indices follows. -/
instance reach_decidable (a c:Nat) : Decidable (Reach a c) :=
  decidable_of_iff (∃ n : Fin (a+c+1), run n.val=some (a,c)) (finite_iff a c)

#print axioms BB6.P1Rank.reach_iff_bounded_run
#print axioms BB6.P1Rank.run_reachable
#print axioms BB6.P1Rank.no_positive_cycle
#print axioms BB6.P1Rank.reach_decidable
end BB6.P1Rank

#eval decide (BB6.Agent1.Reach 2 1)
#eval decide (BB6.Agent1.Reach 2 5)
#eval decide (BB6.Agent1.Reach 0 0)
