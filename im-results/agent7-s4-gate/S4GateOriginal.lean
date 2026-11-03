module

public import BusyBeaver.BB6.Accelerations.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

@[expose] public section

namespace BB6.Agent7S4Gate

open BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF
open BusyBeaver.Stack

/-- Little-endian weighted sum of the left stack's unary-block digits. -/
def weighted : List Nat → Nat
  | [] => 0
  | b :: rest => b + 2 * weighted rest

/-- An even positive current digit immediately terminates the high-level
    inner drain with a defined return, for every arbitrary left/right suffix. -/
theorem even_step_some (a : Nat) (L R : List Nat)
    (ha : 2 ≤ a) (he : a % 2 = 0) :
    stepEpoch a L R ≠ none := by
  cases L with
  | nil =>
      rw [stepEpoch]
      simp [show ¬ a ≤ 1 by omega, he]
  | cons b tail =>
      rw [stepEpoch]
      simp [he]

/-- Source-faithful first odd digit consumption; the right-stack contents
    do not influence which parity branch is selected. -/
theorem odd_cons (q b : Nat) (L R : List Nat) :
    stepEpoch (2 * q + 1) (b :: L) R =
      stepEpoch (b + q + 1) L (0 :: bumpHeadBy q R) := by
  have hf : (2 * q + 1) / 2 = q := by omega
  have ho : (2 * q + 1) % 2 ≠ 0 := by omega
  rw [stepEpoch]
  simp [hf, ho]

/-- Universal necessary halting congruence for the authentic S4 source.
    All partial binary carries in an odd-digit drain must be integral.
    This is a statement over the exact imported, original-machine-certified
    stepEpoch, and it holds for *every* right stack R. -/
theorem halt_requires_binary_divisibility (L : List Nat) :
    ∀ (q : Nat) (R : List Nat),
      stepEpoch (2*q+1) L R = none →
      2 ^ L.length ∣ q + weighted L := by
  induction L with
  | nil =>
      intro q R h
      simp [weighted]
  | cons b L ih =>
      intro q R h
      rw [odd_cons] at h
      by_cases hp : (q + b) % 2 = 0
      · have hq : b + q + 1 = 2 * ((q+b)/2) + 1 := by omega
        rw [hq] at h
        obtain ⟨k, hk⟩ := ih ((q+b)/2) (0 :: bumpHeadBy q R) h
        refine ⟨k, ?_⟩
        simp only [weighted, List.length_cons, Nat.pow_succ]
        calc
          q + (b + 2 * weighted L)
              = 2 * (((q+b)/2) + weighted L) := by omega
          _ = 2 * (2 ^ L.length * k) := by rw [hk]
          _ = (2 ^ L.length * 2) * k := by ring
      · have he : (b+q+1)%2=0 := by omega
        have htwo : 2 ≤ b+q+1 := by omega
        exact False.elim ((even_step_some (b+q+1) L
          (0 :: bumpHeadBy q R) htwo he) h)

#print axioms BB6.Agent7S4Gate.odd_cons
#print axioms BB6.Agent7S4Gate.halt_requires_binary_divisibility

end BB6.Agent7S4Gate
