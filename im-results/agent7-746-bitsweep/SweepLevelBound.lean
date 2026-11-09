import SweepSameAddress

namespace CascadeFastReturn
open CascadeBitSweep

/-- Exact source-reset paths whose address remains at a fixed dyadic level. -/
inductive SameLevelPath (k : Nat) : Nat → Nat → Nat → Prop where
  | base (h : Nat) (hk : firstFailIndex h=k) : SameLevelPath k h h 0
  | next {h u v n : Nat} (hu : SameLevelPath k h u n)
      (he : bitOutcome u=some v) (hv : firstFailIndex v=k) :
      SameLevelPath k h v (n+1)

/-- Every fixed-level path has the declared dyadic address at its endpoint. -/
theorem same_level_path_last (k h u n : Nat)
    (hp : SameLevelPath k h u n) : firstFailIndex u=k := by
  induction hp with
  | base hk => exact hk
  | next hpath he hv ih => exact hv

/-- Every same-level first reset divides the exact deficit by two. -/
theorem same_level_path_exact_deficit (k h u n : Nat)
    (hp : SameLevelPath k h u n) :
    deficitAt k h=2^n*deficitAt k u := by
  induction hp with
  | base hk => simp
  | next hpath he hv ih =>
    have hk := same_level_path_last k _ _ _ hpath
    have hh := (same_address_forces_half_deficit _ _ he (hk.trans hv.symm)).2
    rw [hk] at hh
    rw [ih, hh, Nat.pow_succ]
    ac_rfl

/-- No fixed dyadic sweep level can support more successive reset edges
    than the binary logarithm of its initial dyadic upper-band deficit. -/
theorem same_level_path_length_log_bound (k h u n : Nat)
    (hp : SameLevelPath k h u n) :
    n ≤ Nat.log2 (deficitAt k h) := by
  have hdef := same_level_path_exact_deficit k h u n hp
  have hlast := same_level_path_last k h u n hp
  have hh := (firstFailIndex_spec u).2
  rw [hlast] at hh
  have hd : 1≤deficitAt k u := by
    dsimp [deficitAt]
    omega
  have hp2 : 2^n ≤ deficitAt k h := by
    rw [hdef]
    have hmul := Nat.mul_le_mul_left (2^n) hd
    simpa using hmul
  have hz : 0<deficitAt k h := by
    have hpower : 1≤2^n := Nat.one_le_pow n 2 (by decide)
    omega
  exact (Nat.le_log2 (by omega : deficitAt k h ≠ 0)).2 hp2

#print axioms same_level_path_exact_deficit
#print axioms same_level_path_length_log_bound
end CascadeFastReturn
