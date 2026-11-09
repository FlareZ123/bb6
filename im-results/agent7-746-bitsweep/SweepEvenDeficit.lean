import SweepBitOutcome

namespace CascadeFastReturn
open CascadeBitSweep

def deficitAt (k h : Nat) := 8*2^k+k-h

/-- Every even successful reset exactly halves its old address's deficit,
    regardless of whether the successor's address immediately increases. -/
theorem bitOutcome_even_deficit_halves (h k u : Nat)
    (hk : firstFailIndex h=k)
    (heven : (h+k)%2=0)
    (hout : bitOutcome h = some u) :
    deficitAt k h = 2*deficitAt k u := by
  have hhigh := (firstFailIndex_spec h).2
  rw [hk] at hhigh
  have hnot : h+k+4 ≠ 4*2^k := by
    intro hf
    have hn : bitOutcome h = none := by simp [bitOutcome, hk, hf]
    rw [hn] at hout
    cases hout
  have heq : u=4*2^k+(h+k)/2 := by
    simp [bitOutcome, hk, hnot, heven] at hout
    exact hout.symm
  have htwou : 2*u=8*2^k+h+k := by
    rw [heq]
    omega
  have hless : h ≤ 8*2^k+k := by omega
  have uless : u ≤ 8*2^k+k := by omega
  dsimp [deficitAt]
  omega

#print axioms bitOutcome_even_deficit_halves
end CascadeFastReturn
