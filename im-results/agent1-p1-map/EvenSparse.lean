import EvenFull
namespace BB6.Agent1

/-- In the right-counter residue matching its exponential left index,
    every genuinely blank-reachable even hub lies on a sparse second
    exponent ladder of odd exponents. All other counters are excluded. -/
theorem even_hub_sparse_counter_classification (b d:Nat) (hr:Reach b d)
    (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0) :
    ∃ j:Nat, b+12=14*2^j ∧
      (2≤j → d%4=(2*j+2)%4 → ∃ t:Nat,
        j≤t ∧ t%2=1 ∧ d+14*2^j=14*2^t+2*j+6) := by
  obtain ⟨j,s,hs,hpow,hmass,hclass⟩:=
    even_hub_odd_reset_dichotomy b d hr hb hdpos hdeven
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
  exact ⟨t,htge,htodd,hdval⟩

/-- In an odd hub-index sector, the only dangerous-residue counter
    below the next odd-power jump is the precise smallest exception. -/
theorem even_hub_odd_index_single_low_counter (b d:Nat) (hr:Reach b d)
    (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0) :
    ∃ j:Nat, b+12=14*2^j ∧
      (2≤j → j%2=1 → d%4=(2*j+2)%4 →
       d<42*2^j+2*j+6 → d=2*j+6) := by
  obtain ⟨j,hpow,hclass⟩:=even_hub_sparse_counter_classification b d hr hb hdpos hdeven
  refine ⟨j,hpow,?_⟩
  intro hj hjodd heq hsmall
  obtain ⟨t,htge,htodd,hdval⟩:=hclass hj heq
  have htj:t=j := by
    by_cases hjt:t=j
    · exact hjt
    · have hlarge : j+2≤t := by omega
      have hpowle:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hlarge
      have hp : 2^(j+2)=4*2^j := by
        rw [Nat.pow_add]
        simp only [Nat.reducePow]
        omega
      omega
  rw [htj] at hdval
  omega

#print axioms BB6.Agent1.even_hub_sparse_counter_classification
#print axioms BB6.Agent1.even_hub_odd_index_single_low_counter
end BB6.Agent1
