import SafeStep
import Init.Omega
namespace Agent9CoreCounter
open Agent9Val

/-- A 108-bit synthetic counter (not either genuine blank-root counter). -/
def q : Nat := 208596292082770133442964332173824
/-- Maximal factor-of-four-free core. -/
def u : Nat := 814829265948320833761579422554

private theorem q_valid : 16 ≤ q := by decide
private theorem q_nonzero : q%3≠0 := by decide
private theorem q_one : q%3=1 := by decide
private theorem q_four_core : q=4^4*u ∧ u%4≠0 ∧ u<3^63 := by decide
private theorem fatal_divisibility : 3^69 ∣ 4*q-13 := by decide

theorem core_below_exponential : q=4^4*u ∧ u%4≠0 ∧ u<3^63 := q_four_core

theorem exact_exit : steps 69 (some (q,63))=none := by
  have h := (exact_nonzero_fatal_gate q 63 q_valid q_nonzero).mp
    (by simpa [incr,penaltyNZ,q_one] using fatal_divisibility)
  simpa [incr,q_one] using h

theorem no_earlier_exit (n : Nat) (hn : n<69) :
    ∃s, steps n (some (q,63))=some s := by
  have h : 63+incr q < (split3 (onNZ q)).1 :=
    (nonzero_fatal_divisibility q 63 q_valid q_nonzero).mp
      (by simpa [incr,penaltyNZ,q_one] using fatal_divisibility)
  have hh := (nonzero_core_first_transfer q 63 q_valid q_nonzero h).2
  apply hh n
  simpa [incr,q_one] using hn

#print axioms core_below_exponential
#print axioms exact_exit
#print axioms no_earlier_exit
end Agent9CoreCounter
