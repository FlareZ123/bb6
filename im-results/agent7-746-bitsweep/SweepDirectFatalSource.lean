import SweepOddFatalNine
import SweepDirectFatalArithmetic

namespace CascadeFastReturn
open CascadeBitSweep
open CascadeDirectFatalArithmetic

/-- Every direct odd source first-reset entry into a fatal dyadic level >=2
    has a 3-adic factor of at least 3² in its output offset. The t=0
    inverse quotient would lie strictly in the gap (2*2^k,3*2^k),
    disjoint from all source odd inverse quotient bands. -/
theorem odd_direct_fatal_mod_nine (a entry k : Nat)
    (hodd : (a+firstFailIndex a)%2=1)
    (hout : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hf : fatalAt entry)
    (hk2 : 2≤k) :
    (2*entry+5)%9=0 := by
  let j := firstFailIndex a
  let q := 4*2^j+(a+j)/2+3
  let t := (stripTwos q).1
  let d := (stripTwos q).2
  have hnot : a+j+4≠4*2^j := by
    intro heq
    have hn : bitOutcome a=none := by simp [bitOutcome, j, heq]
    rw [hn] at hout
    cases hout
  have hpar : (a+j)%2=1 := hodd
  have hentry : entry=(3^(t+1)*d-5)/2 := by
    have hne : (a+j)%2≠0 := by omega
    simp [bitOutcome, j, hnot, hne] at hout
    exact hout.symm
  have hqpos : 0<q := by dsimp [q]; omega
  have hfactor : q=2^t*d := (stripTwos_spec q hqpos).1
  have hdodd : d%2=1 := (stripTwos_spec q hqpos).2
  have hlow : 4*2^j≤a+j+4 := firstFailIndex_low a
  have hq7 : 7≤2^t*d := by
    rw [←hfactor]
    dsimp [q]
    have hp : 1≤2^j := Nat.one_le_pow j 2 (by decide)
    omega
  have heq := CascadeResetInverse.odd_output_equation t d hdodd hq7
  have heqentry : 2*entry+5=3^(t+1)*d := by rw [hentry]; exact heq
  have hband := CascadeResetInverse.odd_inverse_band a j (by exact hlow)
    (by exact (firstFailIndex_spec a).2) hnot hpar
  change (6*2^j+1≤q ∧ q≤8*2^j-1) ∧
    2*q=8*2^j+a+j+5 at hband
  have htpos : 1≤t := by
    by_cases htzero : t=0
    · have hdq : q=d := by rw [hfactor, htzero]; simp
      have heq3 : 3*q=2*entry+5 := by
        calc
          3*q = 3*d := by rw [hdq]
          _ = 3^(t+1)*d := by simp [htzero]
          _ = 2*entry+5 := heqentry.symm
      have hfheight : entry+k+4=4*2^k := by
        dsimp [fatalAt] at hf
        rw [hk] at hf
        exact hf
      exact False.elim (fatal_no_odd_zero_valuation k j entry q
        hk2 hfheight heq3 hband.1)
    · omega
  have hdiv9 : 9∣3^(t+1)*d := by
    have hge : 2≤t+1 := by omega
    obtain ⟨r,hr⟩ := Nat.pow_dvd_pow 3 hge
    refine ⟨r*d, ?_⟩
    rw [hr]
    simp only [show (3:Nat)^2=9 by decide]
    ac_rfl
  rw [heqentry]
  exact Nat.mod_eq_zero_of_dvd hdiv9

/-- A direct odd C-reset into a fatal threshold of level k>=2 is possible
    only when k is 4 or 5 modulo 18, including for arbitrary synthetic
    predecessors. Root reachability is neither assumed nor implied. -/
theorem odd_direct_fatal_sector (a entry k : Nat)
    (hodd : (a+firstFailIndex a)%2=1)
    (hout : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hf : fatalAt entry)
    (hk2 : 2≤k) :
    k%18=4 ∨ k%18=5 := by
  have he : entry+k+4=4*2^k := by
    dsimp [fatalAt] at hf
    rw [hk] at hf
    exact hf
  exact fatal_nine_sector k entry he
    (odd_direct_fatal_mod_nine a entry k hodd hout hk hf hk2)

#print axioms odd_direct_fatal_mod_nine
#print axioms odd_direct_fatal_sector

end CascadeFastReturn
