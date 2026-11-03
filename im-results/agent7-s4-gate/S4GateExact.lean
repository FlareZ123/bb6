module

public import Agent7S4GateOriginal

@[expose] public section

namespace BB6.Agent7S4Gate

open BusyBeaver.Stack
open BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

private theorem pow2_double (n m : Nat) :
    2 ^ (n+1+m) = 2 * 2 ^ (n+m) := by
  rw [show n+1+m = n+m+1 by omega, Nat.pow_succ]
  omega

private theorem pow2_succ_double (n : Nat) :
    2 ^ (n+1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ]
  omega

/-- The empty-left S4 drain halts exactly on binary all-ones odd registers.
    This is the exact original imported recursion, with arbitrary right stack. -/
theorem empty_odd_halt_iff (q : Nat) (R : List Nat) :
    stepEpoch (2*q+1) [] R = none ↔ ∃ m, q+1 = 2^m := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hz : q = 0
    · subst q
      constructor
      · intro _
        exact ⟨0, by decide⟩
      · intro _
        rfl
    · have hlarge : ¬(2*q+1 ≤ 1) := by omega
      have hhalf : (2*q+1)/2=q := by omega
      have hodd : (2*q+1)%2 ≠ 0 := by omega
      have hstep : stepEpoch (2*q+1) [] R =
          stepEpoch q [] (0 :: bumpHeadBy q R) := by
        rw [stepEpoch]
        simp [hlarge, hhalf, hodd]
      rw [hstep]
      by_cases he : q % 2 = 0
      · have hq : 2 ≤ q := by omega
        constructor
        · intro h
          exact False.elim ((even_step_some q [] (0 :: bumpHeadBy q R) hq he) h)
        · rintro ⟨m, hm⟩
          exfalso
          cases m with
          | zero =>
              simp at hm
              omega
          | succ m =>
              rw [Nat.pow_succ] at hm
              omega
      · obtain ⟨r, hr⟩ : ∃ r, q = 2*r+1 := ⟨q/2, by omega⟩
        subst q
        have hlt : r < 2*r+1 := by omega
        have hi := ih r hlt (0 :: bumpHeadBy (2*r+1) R)
        constructor
        · intro h
          obtain ⟨m, hm⟩ := hi.mp h
          refine ⟨m+1, ?_⟩
          rw [Nat.pow_succ]
          omega
        · rintro ⟨m, hm⟩
          cases m with
          | zero =>
              simp at hm
              omega
          | succ m =>
              apply hi.mpr
              refine ⟨m, ?_⟩
              rw [Nat.pow_succ] at hm
              omega

/-- Exact universal S4 high-level halting gate on a finite left digit stack:
    any right stack R, odd a=2q+1 and n=length L. The right stack is provably
    irrelevant, and the weighted stack must hit a power of two.

      stepEpoch (2q+1) L R = none
        iff exists m, q + weighted(L) + 2^n = 2^(n+m).

    Unlike a long-prefix simulation, this describes every possible one-step
    halting configuration, including arbitrarily large stacks. -/
theorem odd_halt_exact (L : List Nat) :
    ∀ (q : Nat) (R : List Nat),
      stepEpoch (2*q+1) L R = none ↔
        ∃ m, q + weighted L + 2 ^ L.length = 2 ^ (L.length+m) := by
  induction L with
  | nil =>
      intro q R
      simpa [weighted] using empty_odd_halt_iff q R
  | cons b L ih =>
      intro q R
      rw [odd_cons]
      by_cases hp : (q+b)%2=0
      · have hq : b+q+1 = 2*((q+b)/2)+1 := by omega
        rw [hq]
        rw [ih ((q+b)/2) (0 :: bumpHeadBy q R)]
        constructor
        · rintro ⟨m, hm⟩
          refine ⟨m, ?_⟩
          have hpow := pow2_double L.length m
          have hsuc := pow2_succ_double L.length
          simp only [weighted, List.length_cons]
          rw [hpow, hsuc]
          omega
        · rintro ⟨m, hm⟩
          refine ⟨m, ?_⟩
          have hpow := pow2_double L.length m
          have hsuc := pow2_succ_double L.length
          simp only [weighted, List.length_cons] at hm
          rw [hpow, hsuc] at hm
          omega
      · have hnot : stepEpoch (b+q+1) L
            (0 :: bumpHeadBy q R) ≠ none :=
          even_step_some (b+q+1) L (0 :: bumpHeadBy q R)
            (by omega) (by omega)
        constructor
        · intro h
          exact False.elim (hnot h)
        · rintro ⟨m, hm⟩
          have hpow := pow2_double L.length m
          have hsuc := pow2_succ_double L.length
          simp only [weighted, List.length_cons] at hm
          rw [hpow, hsuc] at hm
          omega

#print axioms BB6.Agent7S4Gate.empty_odd_halt_iff
#print axioms BB6.Agent7S4Gate.odd_halt_exact

end BB6.Agent7S4Gate
