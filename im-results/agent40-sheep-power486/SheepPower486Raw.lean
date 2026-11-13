import SectionExclusionBridge
import EvenSourceBridge
import SheepPower486Source

namespace BB6.Agent40.SheepPower486

/-- Exponents in the sixth 3-adic stratum whose exact even-source fiber is empty. -/
def SixthStratumExcluded (j : Nat) : Prop :=
  ∃ t : Nat, j = 486*t ∧ 1≤t ∧ t%3≠0 ∧ t%4=0 ∧ t%7≠1 ∧ t%9≠2

/-- Every exponent in the new sixth-stratum family is unreachable in the
    authentic blank-even return graph. -/
theorem sixth_stratum_unreachable (j : Nat)
    (h : SixthStratumExcluded j) :
    ¬ SheepEven.EvenReach 10 (2^j) := by
  rcases h with ⟨t,rfl,ht,ht3,ht4,ht7,ht9⟩
  exact SheepPower486.blank_even_cannot_hit_sixth t ht ht3 ht4 ht7 ht9

/-- Original blank-tape halting is equivalent to reaching a power outside both
    the older 157/360 periodic exclusion and the new sixth-stratum family. -/
theorem raw_halts_iff_nonexcluded_power :
    BusyBeaver.IsHalt BB6.Agent22.SheepSource.Source.target ↔
      ∃ j : Nat, 2≤j ∧
        ¬ SheepInverse.PeriodicExcluded j ∧
        ¬ SixthStratumExcluded j ∧
        SheepEven.EvenReach 10 (2^j) := by
  rw [BB6.Agent16.SheepEvenSource.raw_halts_iff_even_power]
  constructor
  · rintro ⟨j,hj,hr⟩
    refine ⟨j,hj,?_,?_,hr⟩
    · intro hp
      have he : (2^j)%2=0 := by
        have hj' : j=(j-1)+1 := by omega
        rw [hj', Nat.pow_succ]
        simp
      obtain ⟨n,p⟩ := (SheepEven.blank_even_reach_iff he).mpr hr
      exact (BB6.Agent22.SectionExclusionBridge.excluded_power_unreachable j hp)
        (BB6.Agent16.SheepEvenSource.even_steps_to_reach p)
    · intro hs
      exact sixth_stratum_unreachable j hs hr

  · rintro ⟨j,hj,_,_,hr⟩
    exact ⟨j,hj,hr⟩

#print axioms sixth_stratum_unreachable
#print axioms raw_halts_iff_nonexcluded_power

end BB6.Agent40.SheepPower486
