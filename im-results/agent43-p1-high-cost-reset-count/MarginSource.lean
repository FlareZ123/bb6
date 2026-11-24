import ExactEndpoint
import P1CarryBlankArithmetic
import P1Gate
import MarginCert

/-! Generalize Agent50's critical blank-reachability argument from
    early small-carry extinction to arbitrary full-P cost certificates.
    The interface deliberately retains all original OddCone guards. -/
namespace BB6.Agent43MarginSource
open BB6.Agent28FullPrefix BB6.Agent43CarryCert
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction BB6.P1CarryExact

theorem states_eq (Q j : Nat) (cs : List Nat) (K : Nat) :
    states Q j cs K = fullCarryStates Q j cs K := by
  induction K generalizing j cs with
  | zero => rfl
  | succ k ih => exact ih (j+1) (step Q j cs)

theorem critical_root_mass (n : Nat) (hn : 14≤n) :
    criticalLeft n+3+2*n+13=14*2^n := by
  unfold criticalLeft
  have hp := pow2_ge_1100_mul n hn
  omega

theorem oddcone_endpoint (n b d m : Nat) (hn : 14≤n)
    (h : OddCone (criticalLeft n) 3 b d m) :
    (d-1)/2 ∈ fullCarryStates (7*2^n-(n+3)) 0 [1] m := by
  induction h with
  | root => simp [fullCarryStates]
  | parent bp dp mp t k c hp hb hb4 hd hi hk hc ih =>
      have hmass0 := odd_cone_mass _ _ bp dp mp hp
      have hroot := critical_root_mass n hn
      have hmass : bp+dp+2*mp+2*n+13=14*2^n := by omega
      have hpower := (inverseAt_iff_power_mass bp dp t k c
        (by omega) hb4 hd).mp hi
      have heq := exact_endpoint_block_equation n bp dp mp t c hb4 hd hc hmass hpower.1
      have hcarry := fullCarry_append_block _ mp _ _ t ih heq
      simpa only [show c+4-1=c+3 by omega] using hcarry

def GateConditions (n K : Nat) : Prop :=
  ∀ b d m, OddCone (criticalLeft n) 3 b d m →
    m<K ∧ d≠5 ∧ n+3*K+10≤b/4

theorem conditions_of_margin (n K : Nat) (hn : 14≤n)
    (hcert : MarginSafe (7*2^n-(n+3)) (requiredMargin n K) 0 [1] K []) :
    GateConditions n K := by
  intro b d m h
  have he := oddcone_endpoint n b d m hn h
  rw [← states_eq] at he
  obtain ⟨hlt,hno,hmarg⟩ := MarginSafe.member hcert he
  have hmass0 := odd_cone_mass _ _ b d m h
  have hroot := critical_root_mass n hn
  have hmass : b+d+2*m+2*n+13=14*2^n := by omega
  have hd := source_odd_right _ _ _ _ _ (by decide) h
  have hp := pow2_ge_1100_mul n hn
  refine ⟨hlt, ?_, left_from_carry n K b d m hd (by omega) hmass hmarg⟩
  intro hfive
  apply hno
  simp [hfive]

theorem inverse_cost_of_conditions (n K b d m t k c : Nat)
    (hg : GateConditions n K) (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c)) : m+t<K := by
  obtain ⟨hlt,_,hlarge⟩ := hg b d m h
  cases t with
  | zero => simpa using hlt
  | succ t =>
    obtain ⟨k0,c0,hi0,hc0⟩ := inverse_prev_odd b d t k c hi
    have hk := inverse_k_lower b d t k0 c0 hi0
    have hc := OddCone.parent b d m t k0 c0 h (by omega) hb4 hd hi0 (by omega) hc0
    have hcost := (hg _ _ _ hc).1
    omega

theorem no_one_of_conditions (n K b d m k : Nat)
    (hg : GateConditions n K) (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) : ¬ GAncestor b d k 1 := by
  intro ha
  obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
  have hlarge := (hg b d m h).2.2
  have hk := ancestor_k_lower b d k 1 ha
  have hc := OddCone.parent b d m t k 1 h (by omega) hb4 hd hi (by omega) (by decide)
  exact (hg _ _ _ hc).2.1 (by decide)

theorem even_gap_of_conditions (n K b d m t k c : Nat)
    (hn : 14≤n) (hg : GateConditions n K) (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 7*2^n<2*k+8 ∧ 2*k+8<14*2^n := by
  have hlarge := (hg b d m h).2.2
  have hcost := inverse_cost_of_conditions n K b d m t k c hg h hb4 hd hi
  have hmass := odd_cone_mass _ _ b d m h
  have hroot := critical_root_mass n hn
  have hMass : b+d+2*m+2*n+13=14*2^n := by omega
  have hback := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hpower := inverseAt_power b d t k c hi
  have ht : 1≤t := by
    by_cases hzero : t=0
    · subst t; simp at hpower; omega
    · omega
  have hpow : 2≤2^t := by
    have hp := Nat.pow_le_pow_right (show 0<2 by decide) ht
    simpa using hp
  have hcBound : 2*(c+3)≤d+b/2+3 := by
    rw [hpower]
    exact Nat.mul_le_mul_right (c+3) hpow
  omega

theorem even_no_power_of_conditions (n K b d m t k c j : Nat)
    (hn : 14≤n) (hg : GateConditions n K) (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 2*k+8≠14*2^j := by
  obtain ⟨hl,hr⟩ := even_gap_of_conditions n K b d m t k c hn hg h hb4 hd hi hc
  intro he
  by_cases hj : n≤j
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) hj
    omega
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show j≤n-1 by omega)
    have hsplit : 2^n=2*2^(n-1) := by
      have heq : n=n-1+1 := by omega
      calc
        2^n = 2^(n-1+1) := congrArg (fun i : Nat => 2^i) heq
        _ = _ := by rw [Nat.pow_succ]; ac_rfl
    omega

/-- Generalized Agent50 source induction. No K≤n restriction. -/
theorem cone_no_reach_of_conditions (n K r : Nat) (hn : 14≤n)
    (hg : GateConditions n K) :
    ∀ b d m, K-m=r → OddCone (criticalLeft n) 3 b d m → ¬ BB6.Agent1.Reach b d := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro b d m hr h hReach
    obtain ⟨hcost,_,hlarge⟩ := hg b d m h
    have hrootEven : criticalLeft n%2=0 := by
      unfold criticalLeft
      have hp := pow2_ge_1100_mul n hn
      omega
    have hbe := source_even_left _ _ _ _ _ hrootEven h
    have hdo := source_odd_right _ _ _ _ _ (by decide) h
    have hpar := BB6.Agent1.reachable_even_mod4 b d hReach (by omega) hbe
    have hb4 : b%4=0 := by rcases hpar with h2 | h4 <;> omega
    have hno : ∀ k, ¬ GAncestor b d k 1 := fun k =>
      no_one_of_conditions n K b d m k hg h hb4 hdo
    obtain ⟨k,c,ha,hc,hpre⟩ := BB6.Agent50P1.positive_G_feeder b d
      (by omega) hb4 (by omega) hno hReach
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
    have hk := inverse_k_lower b d t k c hi
    by_cases heven : c%2=0
    · obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (2*k-4) (c+4)
        hpre (by omega) (by omega) (by omega)
      exact even_no_power_of_conditions n K b d m t k c j hn hg h hb4 hdo hi heven (by omega)
    · have hchild := OddCone.parent b d m t k c h (by omega) hb4 hdo hi (by omega) (by omega)
      have hnew := (hg _ _ _ hchild).1
      exact ih (K-(m+t+1)) (by omega) _ _ _ rfl hchild hpre

theorem critical_hub_no_reach_of_margin (n K : Nat) (hn : 14≤n)
    (hcert : MarginSafe (7*2^n-(n+3)) (requiredMargin n K) 0 [1] K []) :
    ¬ BB6.Agent1.Reach (criticalLeft n) 3 :=
  cone_no_reach_of_conditions n K K hn (conditions_of_margin n K hn hcert)
    _ _ 0 (by omega) OddCone.root

/-- Every even critical index satisfying the full-P certificate is
    excluded from the authentic source reset reachability relation. -/
theorem critical_reset_no_reach_of_margin (n K : Nat) (hn : 14≤n) (heven : n%2=0)
    (hcert : MarginSafe (7*2^n-(n+3)) (requiredMargin n K) 0 [1] K []) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro h
  have hp := pow2_ge_1100_mul n hn
  have he : (2:Nat)^n%2=0 := by
    apply Nat.dvd_iff_mod_eq_zero.mp
    have hd := Nat.pow_dvd_pow 2 (show 1≤n by omega)
    simpa using hd
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hmod : d%4=2 := by dsimp [d]; omega
  have hreach := BB6.Agent50P1.critical_target_implies_three d hd hmod h
  have heq : d-6=criticalLeft n := by dsimp [d,criticalLeft]; omega
  rw [heq] at hreach
  exact critical_hub_no_reach_of_margin n K hn hcert hreach

#print axioms oddcone_endpoint
#print axioms conditions_of_margin
#print axioms cone_no_reach_of_conditions
#print axioms critical_reset_no_reach_of_margin
end BB6.Agent43MarginSource
