import ResetOdd
namespace BB6.Agent1

private theorem lin6 (j:Nat) : 2*j+6<7*2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

/-- Uniform reset-origin dichotomy for every authentic blank-reachable
    positive-even-right hub: if its reset seed is 0 mod 4, then the
    corresponding reset exponent is odd and at least the hub exponent. -/
theorem even_hub_odd_reset_dichotomy (b d:Nat) (hr:Reach b d)
    (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0) :
    ∃ j s : Nat, Reach 2 s ∧ b+12=14*2^j ∧ s+2*j+2=b+d ∧
      (2≤j → s%4=0 → ∃ t : Nat,
        t%2=1 ∧ j≤t ∧ d+14*2^j=14*2^t+2*j+6) := by
  obtain ⟨j,s,hs,hpow,hmass⟩:=even_hub_reset_seed b d hr hb hdpos hdeven
  refine ⟨j,s,hs,hpow,hmass,?_⟩
  intro hj hmod
  have hjpow:4≤2^j := by
    have h:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hj
    simpa using h
  have hlinear:2*j+6<7*2^j:=lin6 j
  have hhigh:28≤7*2^j:=by omega
  have hs12:12≤s:=by omega
  obtain ⟨t,ht,htodd⟩:=reset_divfour_odd_exponent s hs hs12 hmod
  have hmass2 : d+14*2^j=14*2^t+2*j+6 := by omega
  have hle:j≤t:=by
    by_cases h:t<j
    · have hbound : t≤j-1:=by omega
      have hpowle:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hbound
      have hpowrel:2^j=2*2^(j-1):=by
        have hj1:j=(j-1)+1:=by omega
        calc
          2^j=2^((j-1)+1):=by congr 1
          _=2*2^(j-1):=by rw [Nat.pow_succ]; omega
      omega
    · omega
  exact ⟨t,htodd,hle,hmass2⟩

/-- For every even positive hub with even exponent j>=2, all small
    right counters in the dangerous mod-four residue class are forbidden.
    The threshold is exponential in j, much stronger than the linear wedge. -/
theorem even_hub_even_index_exponential_gap (b d:Nat) (hr:Reach b d)
    (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0) :
    ∃ j:Nat, b+12=14*2^j ∧
      (2≤j → j%2=0 → d<14*2^j+2*j+6 → d%4≠(2*j+2)%4) := by
  obtain ⟨j,s,hs,hpow,hmass,hclass⟩:=even_hub_odd_reset_dichotomy b d hr hb hdpos hdeven
  refine ⟨j,hpow,?_⟩
  intro hj hjeven hsmall heq
  have hp4:2^j=4*2^(j-2):=by
    have hj2:j=(j-2)+2:=by omega
    calc
      2^j=2^((j-2)+2):=by congr 1
      _=4*2^(j-2):=by rw [Nat.pow_add]; simp only [Nat.reducePow]; omega
  have hbmod:b%4=0:=by rw [hp4] at hpow; omega
  have hsmod:s%4=0:=by omega
  obtain ⟨t,htodd,htge,heqmass⟩:=hclass hj hsmod
  have htge1:j+1≤t:=by omega
  have hpowle:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) htge1
  have hpowrel : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
  omega

#print axioms BB6.Agent1.even_hub_odd_reset_dichotomy
#print axioms BB6.Agent1.even_hub_even_index_exponential_gap
end BB6.Agent1
