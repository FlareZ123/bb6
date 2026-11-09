import SweepOddCross

namespace CascadeFastReturn
open CascadeBitSweep

/-- Every successful exact reset strictly increases the reset height. -/
theorem bitOutcome_strict_direct (h u : Nat)
    (ho : bitOutcome h = some u) : h<u := by
  let k := firstFailIndex h
  have hhigh : h+k+5 < 8*2^k := (firstFailIndex_spec h).2
  by_cases hfat : h+k+4=4*2^k
  · have hh : bitOutcome h = none := by
      simp [bitOutcome, show firstFailIndex h=k from rfl, hfat]
    rw [hh] at ho
    cases ho
  · by_cases heven : (h+k)%2=0
    · have he : bitOutcome h = some (4*2^k+(h+k)/2) := by
        simp [bitOutcome, show firstFailIndex h=k from rfl, hfat, heven]
      have heq : u=4*2^k+(h+k)/2 :=
        (Option.some.inj (he.symm.trans ho)).symm
      omega
    · have hodd : (h+k)%2=1 := by omega
      have hu := bitOutcome_odd_crosses h u ho hodd
      change 8*2^k≤u at hu
      omega

/-- The dyadic sweep address of a genuine successful reset never decreases. -/
theorem bitOutcome_address_monotone (h u : Nat)
    (ho : bitOutcome h = some u) :
    firstFailIndex h ≤ firstFailIndex u :=
  firstFailIndex_mono h u (Nat.le_of_lt (bitOutcome_strict_direct h u ho))

/-- Every odd source-C reset strictly raises its dyadic address. -/
theorem bitOutcome_odd_address_increases (h u : Nat)
    (ho : bitOutcome h = some u)
    (hodd : (h+firstFailIndex h)%2=1) :
    firstFailIndex h < firstFailIndex u :=
  firstFailIndex_gt_of_eight (firstFailIndex h) u (bitOutcome_odd_crosses h u ho hodd)

#print axioms bitOutcome_strict_direct
#print axioms bitOutcome_address_monotone
#print axioms bitOutcome_odd_address_increases
end CascadeFastReturn
