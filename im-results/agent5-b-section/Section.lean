import Lean.Elab.Tactic.Omega

namespace BB6.BSection

def nextB : Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | (0, 0, _) => none
  | (a + 1, 0, c) => some (a, c, 2)
  | (0, 1, c) => some (2 * c + 9, 0, 0)
  | (a + 1, 1, c) => some (a, c, 6)
  | (a, b + 2, c) => some (a, b, c + 3)

/-- Forward-recursive executor for exact macro-collapse lemmas. -/
def iter {α : Type} (f : α → Option α) : Nat → α → Option α
  | 0, s => some s
  | n+1, s => (f s).bind (iter f n)

theorem iter_drain_even (a q c : Nat) :
    iter nextB q (a, 2*q, c) = some (a, 0, c + 3*q) := by
  induction q generalizing c with
  | zero => simp [iter]
  | succ q ih =>
      rw [show 2*(q+1) = 2*q+2 by omega]
      simp only [iter, nextB, Option.bind_some]
      rw [ih]
      have hs : c + 3 + 3*q = c + 3*(q+1) := by omega
      rw [hs]

theorem iter_drain_odd (a q c : Nat) :
    iter nextB q (a, 2*q+1, c) = some (a, 1, c + 3*q) := by
  induction q generalizing c with
  | zero => simp [iter]
  | succ q ih =>
      rw [show 2*(q+1)+1 = (2*q+1)+2 by omega]
      simp only [iter, nextB, Option.bind_some]
      rw [ih]
      have hs : c + 3 + 3*q = c + 3*(q+1) := by omega
      rw [hs]

theorem section_zero_even (a q : Nat) :
    iter nextB (q+1) (a+1, 0, 2*q) = some (a, 0, 3*q+2) := by
  simp only [iter, nextB, Option.bind_some]
  rw [iter_drain_even]
  rw [Nat.add_comm 2 (3*q)]

theorem section_zero_odd (a q : Nat) :
    iter nextB (q+1) (a+1, 0, 2*q+1) = some (a, 1, 3*q+2) := by
  simp only [iter, nextB, Option.bind_some]
  rw [iter_drain_odd]
  rw [Nat.add_comm 2 (3*q)]

theorem section_one_even (a q : Nat) :
    iter nextB (q+1) (a+1, 1, 2*q) = some (a, 0, 3*q+6) := by
  simp only [iter, nextB, Option.bind_some]
  rw [iter_drain_even]
  rw [Nat.add_comm 6 (3*q)]

theorem section_one_odd (a q : Nat) :
    iter nextB (q+1) (a+1, 1, 2*q+1) = some (a, 1, 3*q+6) := by
  simp only [iter, nextB, Option.bind_some]
  rw [iter_drain_odd]
  rw [Nat.add_comm 6 (3*q)]

theorem section_halt (d : Nat) : nextB (0,0,d) = none := by rfl

theorem section_reset (d : Nat) : nextB (0,1,d) = some (2*d+9,0,0) := by rfl

#print axioms BB6.BSection.iter_drain_even
#print axioms BB6.BSection.iter_drain_odd
#print axioms BB6.BSection.section_zero_even
#print axioms BB6.BSection.section_zero_odd
#print axioms BB6.BSection.section_one_even
#print axioms BB6.BSection.section_one_odd
#print axioms BB6.BSection.section_halt
#print axioms BB6.BSection.section_reset
end BB6.BSection
