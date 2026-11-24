import FullConeCertLogic
import OddConeMass
import P1InverseLog
import P1Gate
namespace BB6.Agent23FullCone
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction

def criticalLeft (n : Nat) := 14*2^n-2*n-16

theorem critical_mass (n b d m : Nat) (hn : 14≤n) (h : OddCone (criticalLeft n) 3 b d m) :
    b+d+2*m+2*n+13=14*2^n := by
  have hm := odd_cone_mass _ _ b d m h
  unfold criticalLeft at hm
  have hp := Nat.lt_pow_self (n:=n) (a:=2) (by decide)
  omega

theorem step_mono (Q j : Nat) (cs ds : List Nat) (h : ∀ x, x∈cs → x∈ds) :
    ∀ x, x∈step Q j cs → x∈step Q j ds := by
  intro x hx
  simp only [step,List.mem_flatMap] at hx ⊢
  obtain ⟨c,hc,hx⟩ := hx
  exact ⟨c,h c hc,hx⟩

theorem states_mono (Q j : Nat) (cs ds : List Nat) (h : ∀ x, x∈cs → x∈ds) (k : Nat) :
    ∀ x, x∈states Q j cs k → x∈states Q j ds k := by
  induction k generalizing j cs ds with
  | zero => simpa [states] using h
  | succ k ih => exact ih (j+1) (step Q j cs) (step Q j ds) (step_mono Q j cs ds h)

theorem states_singleton (Q j : Nat) (cs : List Nat) (v k u : Nat) (hv : v∈cs)
    (hu : u∈states Q j [v] k) : u∈states Q j cs k := by
  apply states_mono Q j [v] cs _ k u hu
  intro x hx
  simp at hx
  simpa [hx] using hv

theorem omit_power (Q j u t : Nat) : u∈states Q j [2^t*u] t := by
  induction t generalizing j with
  | zero => simp [states]
  | succ t ih =>
    have hp : 2^(t+1)*u=2*(2^t*u) := by rw [Nat.pow_succ]; ac_rfl
    have hm : 2^t*u∈step Q j [2^(t+1)*u] := by simp [hp,step]
    exact states_singleton Q (j+1) _ _ t u hm (ih (j+1))

theorem block (Q j v u t : Nat) (h : v+(Q-j)=2^(t+1)*u) :
    u∈states Q j [v] (t+1) := by
  have hp : v+(Q-j)=2*(2^t*u) := by rw [h,Nat.pow_succ]; ac_rfl
  have hm : 2^t*u∈step Q j [v] := by simp [step,hp]
  exact states_singleton Q (j+1) _ _ t u hm (omit_power Q (j+1) u t)

theorem append_block (Q m v u t : Nat) (hprev : v∈states Q 0 [1] m)
    (h : v+(Q-m)=2^(t+1)*u) : u∈states Q 0 [1] (m+t+1) := by
  have hm := states_singleton Q m _ v (t+1) u hprev (block Q m v u t h)
  rw [show m+t+1=m+(t+1) by omega, states_add]
  simpa using hm

-- Agent28's ExactEndpoint arithmetic, with a direct OddCone transport below.
theorem exact_endpoint_block_equation (n b d m t c : Nat)
    (hb4 : b%4=0) (hd : d%2=1) (hc : c%2=1)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hpower : d+b/2+3=2^t*(c+3)) :
    (d-1)/2 + ((7*2^n-(n+3))-m) = 2^(t+1)*((c+3)/2) := by
  have hpow2 : 2*(d+b/2+3)=2^(t+1)*(c+3) := by
    rw [hpower, Nat.pow_succ]
    ac_rfl
  have hrec : (d-1)+14*2^n = 2^(t+1)*(c+3)+2*(m+n+3) := by
    rw [← hpow2]
    omega
  have hv : d-1=2*((d-1)/2) := by omega
  have hu : c+3=2*((c+3)/2) := by omega
  have hmul : 2^(t+1)*(2*((c+3)/2))=2*(2^(t+1)*((c+3)/2)) := by ac_rfl
  rw [hv, hu, hmul] at hrec
  omega

theorem source_endpoint (n b d m : Nat) (hn : 14≤n) (h : OddCone (criticalLeft n) 3 b d m) :
    (d-1)/2∈states (7*2^n-(n+3)) 0 [1] m := by
  induction h with
  | root => simp [states]
  | parent bp dp mp t k c hp hb hb4 hd hi hk hc ih =>
    have hmass := critical_mass n bp dp mp hn hp
    have hpow := inverseAt_power bp dp t k c hi
    have heq := exact_endpoint_block_equation n bp dp mp t c hb4 hd hc hmass hpow
    have hcarry := append_block _ mp _ _ t ih heq
    simpa only [show c+4-1=c+3 by omega] using hcarry

theorem ancestor_k_lower (b d k c : Nat) (h : GAncestor b d k c) : b/4-1≤k := by
  induction h with
  | upper k d => omega
  | nest b d k c h ih => omega

theorem inv_lower (b d t k c : Nat) (h : inverseAt b d t = some (k,c)) : b/4-1≤k :=
  ancestor_k_lower b d k c (inverseAt_sound b d t k c h)

theorem prev_odd (b d t k c : Nat) (h : inverseAt b d (t+1) = some (k,c)) :
    ∃ k0 c0, inverseAt b d t = some (k0,c0) ∧ c0%2=1 := by
  simp only [inverseAt] at h
  split at h
  · simp at h
  · next k0 c0 heq =>
    split at h
    · next hcond => exact ⟨k0,c0,heq,hcond.2⟩
    · simp at h

theorem source_facts (n : Nat) (hn : 14≤n) :
    ConeFacts n (OddCone (criticalLeft n) 3) BB6.Agent1.Reach
      (fun b d t k c => inverseAt b d t = some (k,c)) := by
  constructor
  · exact fun b d m h => critical_mass n b d m hn h
  · intro b d m h
    cases h with
    | root =>
      unfold criticalLeft
      have hp := Nat.lt_pow_self (n:=n) (a:=2) (by decide)
      omega
    | parent => omega
  · intro b d m h
    cases h with
    | root => decide
    | parent => omega
  · exact fun b d m h => source_endpoint n b d m hn h
  · exact fun b d m t k c h hb hb4 hd hi hk hc => OddCone.parent b d m t k c h hb hb4 hd hi hk hc
  · exact inv_lower
  · intro b d t k c hb hb4 hd hi
    exact ⟨inverseAt_power b d t k c hi, inverseAt_exact_mass b d t k c hb hb4 hd hi⟩
  · exact prev_odd
  · intro b d hb hd he hr
    rcases BB6.Agent1.reachable_even_mod4 b d hr hd he with h | h
    · omega
    · exact h
  · intro b d hb hb4 hd hno hr
    have hna : ∀ k, ¬GAncestor b d k 1 := by
      intro k ha
      obtain ⟨t,ht,_⟩ := inverseAt_complete b d k 1 ha
      exact hno t k ht
    obtain ⟨k,c,ha,_,hrc⟩ := BB6.Agent50P1.positive_G_feeder b d (by omega) hb4 hd hna hr
    obtain ⟨t,ht,_⟩ := inverseAt_complete b d k c ha
    exact ⟨t,k,c,ht,hrc⟩
  · intro k c hk hc hr
    obtain ⟨a,ha⟩ := BB6.Agent1.even_left_power_shape (2*k-4) (c+4) hr (by omega) (by omega) (by omega)
    exact ⟨a,by omega⟩

theorem source_critical_hub_no_reach (n K : Nat) (hn : 14≤n)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true) :
    ¬BB6.Agent1.Reach (criticalLeft n) 3 :=
  cone_no_reach (source_facts n hn) hn K K hcert _ _ 0 (by omega) OddCone.root

theorem source_critical_reset_no_reach (n K : Nat) (hn : 14≤n) (heven : n%2=0)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true) :
    ¬BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro hr
  have hp := Nat.lt_pow_self (n:=n) (a:=2) (by decide)
  have he : (2:Nat)^n%2=0 := by
    apply Nat.dvd_iff_mod_eq_zero.mp
    have hd := Nat.pow_dvd_pow 2 (show 1≤n by omega)
    simpa using hd
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hmod : d%4=2 := by dsimp [d]; omega
  have h := BB6.Agent50P1.critical_target_implies_three d hd hmod hr
  have hleft : d-6=criticalLeft n := by unfold d criticalLeft; omega
  exact source_critical_hub_no_reach n K hn hcert (hleft ▸ h)

theorem source_critical30_no_reach : ¬BB6.Agent1.Reach 2 (14*2^30-2*30-10) :=
  source_critical_reset_no_reach 30 82 (by decide) (by decide) cert30

#print axioms source_endpoint
#print axioms source_facts
#print axioms source_critical_hub_no_reach
#print axioms source_critical_reset_no_reach
#print axioms source_critical30_no_reach
end BB6.Agent23FullCone
