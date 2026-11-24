import FullConeCertLogic
import ExactEndpoint
import P1CarryWideSource

/-! Draft original-source instantiation. Requires a focused actual-source build;
    the generic logic module is locally kernel checked. -/
namespace BB6.Agent23FullCone
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction
open BB6.Agent28 BB6.Agent28FullPrefix

theorem states_eq (Q j : Nat) (cs : List Nat) (m : Nat) :
    states Q j cs m = fullCarryStates Q j cs m := by
  induction m generalizing j cs with
  | zero => rfl
  | succ m ih =>
    simp only [states, fullCarryStates]
    exact ih (j+1) (step Q j cs)

theorem source_facts (n : Nat) (hn : 14≤n) :
    ConeFacts n (OddCone (BB6.P1CarryExact.criticalLeft n) 3)
      BB6.Agent1.Reach (fun b d t k c => inverseAt b d t = some (k,c)) where
  mass := by
    intro b d m h
    have hm := odd_cone_mass _ _ b d m h
    unfold BB6.P1CarryExact.criticalLeft at hm
    have hp := BB6.P1CarryExact.pow2_ge_1100_mul n hn
    omega
  evenLeft := by
    intro b d m h
    have he : BB6.P1CarryExact.criticalLeft n%2=0 := by
      unfold BB6.P1CarryExact.criticalLeft
      have hp := BB6.P1CarryExact.pow2_ge_1100_mul n hn
      omega
    exact BB6.P1CarryExact.source_even_left _ _ _ _ _ he h
  oddRight := by
    intro b d m h
    exact BB6.P1CarryExact.source_odd_right _ _ _ _ _ (by decide) h
  endpoint := by
    intro b d m h
    obtain ⟨z,hz⟩ := odd_cone_has_count _ _ b d m h
    rw [states_eq]
    exact source_full_carry_endpoint n b d m z hn hz
  child := by
    intro b d m t k c h hb hb4 hd hi hk hc
    exact OddCone.parent b d m t k c h hb hb4 hd hi hk hc
  invLower := BB6.P1CarryExact.inverse_k_lower
  invEquations := by
    intro b d t k c hb hb4 hd hi
    exact (inverseAt_iff_power_mass b d t k c hb hb4 hd).mp hi
  prevOdd := BB6.P1CarryExact.inverse_prev_odd
  reachableMod4 := by
    intro b d hb hd he hr
    have hpar := BB6.Agent1.reachable_even_mod4 b d hr (by omega) he
    rcases hpar with h2 | h4 <;> omega
  feeder := by
    intro b d hb hb4 hd hnone hr
    have hno : ∀ k, ¬ GAncestor b d k 1 := by
      intro k ha
      obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
      exact hnone t k hi
    obtain ⟨k,c,ha,hc,hpre⟩ := BB6.Agent50P1.positive_G_feeder b d
      (by omega) hb4 (by omega) hno hr
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
    exact ⟨t,k,c,hi,hpre⟩
  evenPower := by
    intro k c hk hc hr
    obtain ⟨a,ha⟩ := BB6.Agent1.even_left_power_shape (2*k-4) (c+4)
      hr (by omega) (by omega) (by omega)
    exact ⟨a,by omega⟩

theorem source_critical_hub_no_reach (n K : Nat) (hn : 14≤n)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true) :
    ¬ BB6.Agent1.Reach (BB6.P1CarryExact.criticalLeft n) 3 :=
  cone_no_reach (source_facts n hn) hn K K hcert _ _ 0 (by omega) OddCone.root

theorem source_critical_reset_no_reach (n K : Nat) (hn : 14≤n) (heven : n%2=0)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro h
  have hp := BB6.P1CarryExact.pow2_ge_1100_mul n hn
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hmod : d%4=2 := by dsimp [d]; omega
  have hreach := BB6.Agent50P1.critical_target_implies_three d hd hmod h
  have heq : d-6=BB6.P1CarryExact.criticalLeft n := by
    dsimp [d,BB6.P1CarryExact.criticalLeft]; omega
  rw [heq] at hreach
  exact source_critical_hub_no_reach n K hn hcert hreach

theorem source_critical30_no_reach :
    ¬ BB6.Agent1.Reach 2 (14*2^30-2*30-10) :=
  source_critical_reset_no_reach 30 82 (by decide) (by decide) cert30

#print axioms source_facts
#print axioms source_critical_hub_no_reach
#print axioms source_critical_reset_no_reach
#print axioms source_critical30_no_reach
end BB6.Agent23FullCone
