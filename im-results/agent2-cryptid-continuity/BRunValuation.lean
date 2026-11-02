import Lean

namespace BB6.CryptidBRun

/-- The exact unary-length update in the source-certified B return. -/
def BStep (n m : Nat) : Prop := 3*m = 8*n+11

/-- BStep is precisely the parametrization in Agent 31's original-source `full_B`. -/
theorem step_index {n m : Nat} (h : BStep n m) :
    ∃ k, n = 3*k+2 ∧ m = 8*k+9 := by
  dsimp [BStep] at h
  refine ⟨n/3, ?_⟩
  omega

inductive BRun : Nat → Nat → Nat → Prop
| zero (n : Nat) : BRun 0 n n
| succ {j n m z : Nat} (h : BStep n m) (tail : BRun j m z) : BRun (j+1) n z

private theorem single_scale {n m : Nat} (h : BStep n m) :
    3*(5*m+11) = 8*(5*n+11) := by
  dsimp [BStep] at h
  omega

/-- A run of j consecutive B branches has an exact conserved rational coordinate. -/
theorem run_scale {j n z : Nat} (h : BRun j n z) :
    3^j*(5*z+11) = 8^j*(5*n+11) := by
  induction h with
  | zero n => simp
  | @succ j n m z h tail ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    have hs := single_scale h
    calc
      3^j * 3 * (5*z+11) = 3 * (3^j * (5*z+11)) := by ac_rfl
      _ = 3*(8^j*(5*m+11)) := by rw [ih]
      _ = 8^j*(3*(5*m+11)) := by ac_rfl
      _ = 8^j*(8*(5*n+11)) := congrArg (Nat.mul (8^j)) hs
      _ = 8^j*8*(5*n+11) := by ac_rfl

/-- Every B-only run must consume one factor of three per return. -/
theorem run_requires_three_power {j n z : Nat} (h : BRun j n z) :
    3^j ∣ 5*n+11 := by
  have hs := run_scale h
  have hd : 3^j ∣ 8^j*(5*n+11) := ⟨5*z+11, hs.symm⟩
  have hc : (3^j).Coprime (8^j) := (show Nat.Coprime 3 8 by decide).pow j j
  exact hc.dvd_of_dvd_mul_left hd

/-- The necessary power-of-three congruence is also sufficient for a finite B-run. -/
theorem three_power_constructs_run :
    ∀ (j n : Nat), 3^j ∣ 5*n+11 → ∃ z, BRun j n z := by
  intro j
  induction j with
  | zero =>
      intro n h
      exact ⟨n, BRun.zero n⟩
  | succ j ih =>
      intro n h
      rcases h with ⟨q, hq⟩
      let p := 3^j*q
      have hp : 5*n+11 = 3*p := by
        calc
          5*n+11 = 3^(j+1)*q := hq
          _ = (3^j*3)*q := by rw [Nat.pow_succ]
          _ = 3*p := by dsimp [p]; ac_rfl
      let m := n+p
      have hs : BStep n m := by
        dsimp [BStep, m]
        omega
      have hm : 5*m+11 = 8*p := by
        dsimp [m]
        omega
      have hd : 3^j ∣ 5*m+11 := by
        refine ⟨8*q, ?_⟩
        rw [hm]
        dsimp [p]
        ac_rfl
      obtain ⟨z, hz⟩ := ih m hd
      exact ⟨z, BRun.succ hs hz⟩

/-- Exact arithmetic characterization of every finite consecutive B itinerary. -/
theorem run_iff_three_power (j n : Nat) :
    (∃ z, BRun j n z) ↔ 3^j ∣ 5*n+11 := by
  constructor
  · rintro ⟨z, h⟩
    exact run_requires_three_power h
  · exact three_power_constructs_run j n

private theorem pow_three_gt (j : Nat) : j < 3^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

/-- No initial unary length can support indefinitely many B branches. -/
theorem no_long_B_run (n z : Nat) : ¬ BRun (5*n+11) n z := by
  intro h
  have hd := run_requires_three_power h
  have hp : 0 < 5*n+11 := by omega
  have hle : 3^(5*n+11) ≤ 5*n+11 := Nat.le_of_dvd hp hd
  have hgt := pow_three_gt (5*n+11)
  omega

#print axioms step_index
#print axioms run_scale
#print axioms run_requires_three_power
#print axioms run_iff_three_power
#print axioms no_long_B_run
end BB6.CryptidBRun
