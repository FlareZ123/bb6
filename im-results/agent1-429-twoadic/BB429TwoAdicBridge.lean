import H0TwoAdic
import Agent6TwoBurstZero
import Lean.Elab.Tactic.Omega

namespace Agent1TwoAdic

private theorem n_eq_N (q : Nat) :
    Agent6TwoBurstZero.n q = H0TwoAdic.N (q+2) := by
  have hpow : 4 ≤ 2^(q+2) := by
    have hp := Nat.pow_le_pow_right (by omega : 0<2) (by omega : 2≤q+2)
    simpa using hp
  simp only [Agent6TwoBurstZero.n, Agent6TwoBurstZero.k,
    Agent6TwoBurstZero.p, Agent6TwoBurstZero.c, H0TwoAdic.N]
  omega

/-- Exact arithmetic synchronization with the original Agent6
    two-burst synthetic-halting family: q corresponds to c=q+2. -/
theorem demand_eq_three_H0 (q : Nat) :
    Agent6TwoBurstZero.demand q = 3 * H0TwoAdic.H0 (q+2) := by
  let c := q+2
  have hc2 : 2 ≤ c := by omega
  have hn : Agent6TwoBurstZero.n q = H0TwoAdic.N c := n_eq_N q
  have hp : Agent6TwoBurstZero.p q = 2^c := rfl
  have hQ : Agent6TwoBurstZero.Q q = 2^(H0TwoAdic.N c) := by
    simp only [Agent6TwoBurstZero.Q,hn]
  have hN : c+2 ≤ H0TwoAdic.N c := H0TwoAdic.N_large c hc2
  have hbig : 2^(c+2) ≤ 2^(H0TwoAdic.N c) :=
    Nat.pow_le_pow_right (by omega) hN
  rw [Nat.pow_add] at hbig
  have hfirst : 24 * 2^c ≤ 12 * 2^(H0TwoAdic.N c) := by omega
  have hH := H0TwoAdic.H0_identity c hc2
  have hbalance : 3 * H0TwoAdic.H0 c + (24 * 2^c + 3*c) =
      12 * 2^(H0TwoAdic.N c) + 39 := by omega
  have heq : Agent6TwoBurstZero.demand q =
      12 * 2^(H0TwoAdic.N c) - 24 * 2^c + 39 - 3*c := by
    simp only [Agent6TwoBurstZero.demand,hQ,hp]
    rfl
  rw [heq]
  change 12 * 2^(H0TwoAdic.N c) - 24 * 2^c + 39 - 3*c = 3*H0TwoAdic.H0 c
  omega

/-- Synthetic halting initial states are congruent to the true blank
    accelerator seed in both counters modulo any power of two. -/
theorem synthetic_halts_in_zero_twoadic_class (E : Nat) :
    ∃ q, Agent6TwoBurstZero.demand q % 2^E = 0 ∧
      ∃ n a b, BB429.run n (0, Agent6TwoBurstZero.demand q) = some (a,b) ∧
        BB429.next (a,b) = none := by
  obtain ⟨c,hc,hr⟩ := H0TwoAdic.H0_all_two_power_residues E 0
  let q := c-2
  have hqc : q+2=c := by dsimp [q]; omega
  refine ⟨q, ?_, Agent6TwoBurstZero.full_source_synthetic_halt q⟩
  rw [demand_eq_three_H0 q, hqc, Nat.mul_mod]
  simp only [Nat.zero_mod] at hr
  simp [hr]

/-- A forward-invariant set containing the actual blank seed and all
    inputs congruent to it in the second counter modulo 2^E must
    contain a synthetically halting state. -/
theorem no_halting_excluding_twoadic_forward_invariant
    (E : Nat) (P : BB429.State → Prop)
    (hseed : ∀ w, w % 2^E = 0 → P (0,w))
    (hforward : ∀ s t, P s → BB429.next s = some t → P t)
    (havoid : ∀ s, P s → BB429.next s ≠ none) : False := by
  obtain ⟨q,hmod,n,a,b,hr,halt⟩ := synthetic_halts_in_zero_twoadic_class E
  have hstart : P (0, Agent6TwoBurstZero.demand q) := hseed _ hmod
  have hp (n : Nat) :
      ∀ s, BB429.run n (0, Agent6TwoBurstZero.demand q) = some s → P s := by
    induction n with
    | zero =>
      intro s h
      simp only [BB429.run, Option.some.injEq] at h
      subst s
      exact hstart
    | succ n ih =>
      intro s h
      simp only [BB429.run] at h
      cases hs : BB429.run n (0, Agent6TwoBurstZero.demand q) with
      | none => simp [hs] at h
      | some t =>
        simp only [hs, Option.bind_some] at h
        exact hforward t s (ih t hs) h
  exact havoid (a,b) (hp n (a,b) hr) halt

#print axioms no_halting_excluding_twoadic_forward_invariant
#print axioms synthetic_halts_in_zero_twoadic_class
#print axioms demand_eq_three_H0
end Agent1TwoAdic
