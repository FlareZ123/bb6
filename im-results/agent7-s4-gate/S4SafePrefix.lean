module

public import Agent7S4GateOriginal

@[expose] public section

namespace BB6.Agent7S4Gate

open BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

/-- Every normalized S4 section configuration C(3, 5::7::(2h)::S)
    has a defined accelerated next step, for arbitrary h, S and right R.
    This universal shield follows from the all-natural binary gate
    divisibility theorem on the imported, original machine source. -/
theorem normalized_even_third_safe (h : Nat) (S R : List Nat) :
    stepEpoch 3 (5 :: 7 :: (2*h) :: S) R ≠ none := by
  intro hnone
  have hd := halt_requires_binary_divisibility
    (5 :: 7 :: (2*h) :: S) 1 R (by simpa using hnone)
  have h8 : 8 ∣ 2 ^ (3 + S.length) := by
    refine ⟨2 ^ S.length, ?_⟩
    rw [pow_add]
    norm_num
  have hlen : (5 :: 7 :: (2*h) :: S).length = 3 + S.length := rfl
  rw [hlen] at hd
  have h8val : 8 ∣ 1 + weighted (5 :: 7 :: (2*h) :: S) :=
    dvd_trans h8 hd
  obtain ⟨k, hk⟩ := h8val
  simp only [weighted] at hk
  omega

#print axioms BB6.Agent7S4Gate.normalized_even_third_safe

end BB6.Agent7S4Gate
