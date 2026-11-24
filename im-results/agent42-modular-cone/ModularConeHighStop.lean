import ModularConeSource
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000

namespace BB6.Agent42ModularCone

/-- Precision used by the sign-free high-stop inverse-cone sieve.
    The first high row (j=1) has one fewer guaranteed bit; for j>=2
    the exact stopping equation supplies the extra bit. -/
def highStopBits (j m : Nat) : Nat :=
  if 2 ≤ j then min 32 (2*m+2) else min 32 (2*m+1)

/-- Executable all-depth source-root exclusion filter for the unified
    high-stop family. It has no j<=3*m+1 or other relative-growth bound. -/
def highStopExcluded (j m : Nat) : Bool :=
  excluded (highStopBits j m) (stopResidue j m)

theorem highStopBits_bound (j m : Nat) (hj : 1 ≤ j) :
    highStopBits j m ≤ 2*m+1 ∨ (2 ≤ j ∧ highStopBits j m ≤ 2*m+2) := by
  by_cases h2 : 2 ≤ j
  · exact Or.inr ⟨h2, by simp [highStopBits, h2]; exact Nat.min_le_right _ _⟩
  · have hj1 : j = 1 := by omega
    subst j
    exact Or.inl (by simp [highStopBits, h2]; exact Nat.min_le_right _ _)

/-- Every accepted adaptive cylinder is absent from the genuine original
    Machine C section orbit. The precision cap is 32 bits, but the theorem
    is uniform in the unbounded stopping parameters. -/
theorem high_stop_excluded (j m k : Nat) (hj : 1 ≤ j)
    (hstop : k+j+3*m+4 = 2^(2*m+2)*(j+2))
    (hc : highStopExcluded j m = true) :
    ¬ BB6.Agent3.CReach (2*j+1) k := by
  let b := highStopBits j m
  have hb := highStopBits_bound j m hj
  have hcheck : excluded b (stopResidue j m) = true := by
    simpa [highStopExcluded, b] using hc
  exact source_stop_cylinder_excluded b j m j m k hb
    (cong_refl b (j:Int)) (cong_refl b (m:Int)) hstop hcheck

/-- Fixed eight-bit version: every accepted pair of residues modulo 256
    excludes every compatible high-stop target with j>=2 and m>=3. -/
def highStopExcluded8 (j m : Nat) : Bool :=
  excluded 8 (stopResidue j m)

theorem high_stop_excluded8 (j m k : Nat) (hj : 2 ≤ j) (hm : 3 ≤ m)
    (hstop : k+j+3*m+4 = 2^(2*m+2)*(j+2))
    (hc : highStopExcluded8 j m = true) :
    ¬ BB6.Agent3.CReach (2*j+1) k :=
  source_stop_cylinder_excluded 8 j m j m k
    (Or.inr ⟨hj, by omega⟩)
    (cong_refl 8 (j:Int)) (cong_refl 8 (m:Int)) hstop
    (by simpa [highStopExcluded8] using hc)

/-- A concrete non-immediate high-stop exclusion beyond the old growth gate:
    unified j=21,m=3 has residue (43,222) modulo 256, so the root is not
    itself in Bad; the inverse cone nevertheless excludes CReach (43,5854). -/
theorem high_stop_example_21_3 : ¬ BB6.Agent3.CReach 43 5854 := by
  have hc : highStopExcluded8 21 3 = true := by decide
  have hs : 5854+21+3*3+4 = 2^(2*3+2)*(21+2) := by norm_num
  exact high_stop_excluded8 21 3 5854 (by omega) (by omega) hs hc

#print axioms high_stop_excluded
#print axioms high_stop_excluded8
#print axioms high_stop_example_21_3

end BB6.Agent42ModularCone
