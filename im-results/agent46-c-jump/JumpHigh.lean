import CLine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

def run : Nat → Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat)
  | 0, s => s
  | n+1, s => run n (s.bind BB6CLine.nextC)

private theorem next_high (a k c : Nat) (ha : 0 < a) (hc : 4 ≤ c) :
    BB6CLine.nextC (a,k,c) = some (a-1,k+1,c-1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  obtain ⟨d, rfl⟩ : ∃ d, c = d+4 := ⟨c-4, by omega⟩
  simp [BB6CLine.nextC]

theorem run_high (n a k c : Nat) (ha : n ≤ a) (hc : n+3 ≤ c) :
    run n (some (a,k,c)) = some (a-n,k+n,c-n) := by
  induction n generalizing a k c with
  | zero => simp [run]
  | succ n ih =>
      have ha0 : 0 < a := by omega
      have hc0 : 4 ≤ c := by omega
      have hh := next_high a k c ha0 hc0
      have ha1 : n ≤ a-1 := by omega
      have hc1 : n+3 ≤ c-1 := by omega
      simp only [run, Option.bind_some, hh]
      rw [ih (a-1) (k+1) (c-1) ha1 hc1]
      simp only [Option.some.injEq, Prod.mk.injEq]
      omega

def highCount (a c : Nat) : Nat := min a (c-3)

def highState (a k c : Nat) : Nat × Nat × Nat :=
  let n := highCount a c
  (a-n,k+n,c-n)

theorem high_count_correct (a k c : Nat) (hc : 4 ≤ c) :
    run (highCount a c) (some (a,k,c)) = some (highState a k c) := by
  have ha : highCount a c ≤ a := Nat.min_le_left _ _
  have hc' : highCount a c+3 ≤ c := by
    have h := Nat.min_le_right a (c-3)
    simp only [highCount] at *
    omega
  exact run_high (highCount a c) a k c ha hc'

theorem high_endpoint (a k c : Nat) (hc : 4 ≤ c) :
    (highState a k c).1 = 0 ∨ (highState a k c).2.2 = 3 := by
  have ha : highCount a c ≤ a := Nat.min_le_left _ _
  have hc' : highCount a c ≤ c-3 := Nat.min_le_right _ _
  simp only [highState]
  unfold highCount at *
  omega

theorem high_rank (a k c : Nat) (hc : 4 ≤ c) :
    let s := highState a k c
    s.1 + 2*s.2.1 + s.2.2 = a + 2*k + c := by
  have ha : highCount a c ≤ a := Nat.min_le_left _ _
  have hc' : highCount a c ≤ c-3 := Nat.min_le_right _ _
  simp only [highState]
  omega

#print axioms run_high
#print axioms high_count_correct
#print axioms high_endpoint
#print axioms high_rank
end BB6.Agent46
