import EvenMiss
namespace BB6.Agent1

private theorem linear_bound (j : Nat) : 2*j+4 < 7*2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

/-- Uniform forbidden low-counter wedge for every reachable even-left,
    positive-even-right P1 hub, expressed using its authentic reset origin. -/
theorem even_hub_low_counter_guard (b d : Nat) (hr : Reach b d)
    (hb : b%2=0) (hdpos : 0<d) (hdeven : d%2=0) :
    ∃ j s : Nat, Reach 2 s ∧ b+12=14*2^j ∧ s+2*j+2=b+d ∧
      (2≤j → d<2*j+6 → s%4≠0) := by
  obtain ⟨j,s,hs,hpow,hmass⟩ := even_hub_reset_seed b d hr hb hdpos hdeven
  refine ⟨j,s,hs,hpow,hmass,?_⟩
  intro hj hdsmall hszero
  have hjpow : 4≤2^j := by
    have hp := Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hj
    simpa using hp
  have hlinear : 2*j+4<7*2^j := linear_bound j
  have hhigh : 28≤7*2^j := by omega
  have hs12 : 12≤s := by omega
  obtain ⟨t,he⟩:=reset_four_power s hs hs12 hszero
  have hhi : s+8 < 14*2^j := by omega
  have hlo : 14*2^(j-1) < s+8 := by
    have hpowrel : 2^j=2*2^(j-1) := by
      have hj1:j=(j-1)+1 := by omega
      calc
        2^j=2^((j-1)+1):= by congr 1
        _=2*2^(j-1):= by rw [Nat.pow_succ]; omega
    omega
  have hfalse : s+8≠14*2^t := by
    intro hx
    by_cases ht:t<j
    · have hord:t≤j-1:=by omega
      have hp:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hord
      omega
    · have hord:j≤t:=by omega
      have hp:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hord
      omega
  exact hfalse he

/-- Small even counter may only occupy one of two parity classes,
    indexed by the whole history of the even-sector doubling chain. -/
theorem even_hub_low_residue (b d : Nat) (hr : Reach b d)
    (hb : b%2=0) (hdpos : 0<d) (hdeven : d%2=0) :
    ∃ j : Nat, b+12=14*2^j ∧
      (2≤j → d<2*j+6 → d%4 ≠ (2*j+2)%4) := by
  obtain ⟨j,s,hs,hpow,hmass,hguard⟩ :=
    even_hub_low_counter_guard b d hr hb hdpos hdeven
  refine ⟨j,hpow,?_⟩
  intro hj hdsmall heq
  have hsnot : s%4≠0 := hguard hj hdsmall
  have hp4:2^j=4*2^(j-2):=by
    have hj2:j=(j-2)+2:=by omega
    calc
      2^j=2^((j-2)+2):=by congr 1
      _=4*2^(j-2):=by rw [Nat.pow_add]; simp only [Nat.reducePow]; omega
  have hbmod:b%4=0:=by rw [hp4] at hpow; omega
  omega

#print axioms BB6.Agent1.even_hub_low_counter_guard
#print axioms BB6.Agent1.even_hub_low_residue
end BB6.Agent1
