import ShiftOdd
namespace BB6.Agent1

private theorem same_pow_index (j k:Nat) (h:2^j=2^k) : j=k := by
  by_cases hlt:j<k
  · have hpow:=Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hlt
    omega
  · by_cases hgt:k<j
    · have hpow:=Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hgt
      omega
    · omega

private theorem linear6quarter (j:Nat) : 2*j+6<7*2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

/-- Stronger global necessary exponent: every genuine even-left right-two
    hub has an index congruent to one modulo four, not merely odd. -/
theorem reachable_even_two_one_mod_four (b:Nat) (hr:Reach b 2)
    (hb:b%2=0) : ∃ j:Nat, b+12=14*2^j ∧ j%4=1 := by
  obtain ⟨j,s,hs,hpow,hmass⟩:=even_two_has_near_critical_reset b hr hb
  obtain ⟨k,hk,hkodd⟩:=reachable_even_two_odd_exponent b hr hb
  have htwo:2^j=2^k:=by omega
  have hjeq:j=k:=same_pow_index j k htwo
  have hjodd:j%2=1:=by simpa only [hjeq] using hkodd
  have hmod:j%4=1:=by
    by_cases h1:j%4=1
    · exact h1
    · have h3:j%4=3:=by omega
      have hj3:3≤j:=by omega
      have hsval:s=14*2^j-2*j-12:=by omega
      have hreset:Reach 2 (14*2^j-2*j-12):=by
        simpa only [←hsval] using hs
      exact False.elim ((blank_no_shifted_odd_reset j hj3 h3) hreset)
  exact ⟨j,hpow,hmod⟩

/-- Every reachable positive reset divisible by four has index 1 modulo 4. -/
theorem reset_divfour_one_mod_four (s:Nat) (hr:Reach 2 s)
    (hs:12≤s) (hmod:s%4=0) :
    ∃ t:Nat, s+8=14*2^t ∧ t%4=1 := by
  obtain ⟨t,ht⟩:=reset_four_power s hr hs hmod
  obtain ⟨b,hrb,hbs⟩:=reset_divfour_requires_even_two s hr hs hmod
  obtain ⟨j,hj,hmodj⟩:=reachable_even_two_one_mod_four b hrb (by omega)
  have hp : 2^t=2^j:=by omega
  have htj:t=j:=same_pow_index t j hp
  exact ⟨t,ht,by simpa only [htj] using hmodj⟩

/-- Full sparse quarter-exponent classification for even-left,
    positive-even-right reachable hubs on the matching mod-four residue. -/
theorem even_hub_sparse_quarter_exponent (b d:Nat) (hr:Reach b d)
    (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0) :
    ∃ j:Nat, b+12=14*2^j ∧
      (2≤j → d%4=(2*j+2)%4 → ∃ t:Nat,
        j≤t ∧ t%4=1 ∧ d+14*2^j=14*2^t+2*j+6) := by
  obtain ⟨j,s,hs,hpow,hmass,hclass⟩:=even_hub_odd_reset_dichotomy b d hr hb hdpos hdeven
  refine ⟨j,hpow,?_⟩
  intro hj heq
  have hp4:2^j=4*2^(j-2):=by
    have hj2:j=(j-2)+2:=by omega
    calc
      2^j=2^((j-2)+2):=by congr 1
      _=4*2^(j-2):=by rw [Nat.pow_add]; simp only [Nat.reducePow]; omega
  have hbmod:b%4=0:=by rw [hp4] at hpow; omega
  have hsmod:s%4=0:=by omega
  obtain ⟨t,htodd,htge,hdval⟩:=hclass hj hsmod
  have hpowj:4≤2^j:=by
    have hp:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hj
    simpa using hp
  have hlinear:2*j+6<7*2^j := linear6quarter j
  have hs12:12≤s:=by omega
  obtain ⟨u,hu,humod⟩:=reset_divfour_one_mod_four s hs hs12 hsmod
  have htval:s+8=14*2^t:=by omega
  have hpe:2^t=2^u:=by omega
  have hte:t=u:=same_pow_index t u hpe
  refine ⟨t,htge,?_,hdval⟩
  simpa only [hte] using humod

#print axioms BB6.Agent1.reachable_even_two_one_mod_four
#print axioms BB6.Agent1.reset_divfour_one_mod_four
#print axioms BB6.Agent1.even_hub_sparse_quarter_exponent
end BB6.Agent1
