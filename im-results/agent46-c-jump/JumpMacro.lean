import JumpHigh
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46
abbrev S := Nat × Nat × Nat

def macroPair (s : S) : Nat × Option S :=
  let (a,k,c) := s
  if 0<a ∧ 4≤c then
    (highCount a c, some (highState a k c))
  else
    (1,BB6CLine.nextC s)

def macroTime (s : S) : Nat := (macroPair s).1
def macroNext (s : S) : Option S := (macroPair s).2

theorem macro_positive (s : S) : 1 ≤ macroTime s := by
  obtain ⟨a,k,c⟩ := s
  simp only [macroTime, macroPair]
  split
  · next h =>
    dsimp
    simp only [highCount]
    omega
  · simp

theorem run_eq (n : Nat) (s : Option S) :
  run n s = BB6.Agent8Section.run BB6CLine.nextC n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [BB6.Agent8Section.run_succ_head]
      change run n (s.bind BB6CLine.nextC) = _
      exact ih _

theorem macro_exact (s : S) :
    BB6.Agent8Section.run BB6CLine.nextC (macroTime s) (some s) = macroNext s := by
  obtain ⟨a,k,c⟩ := s
  by_cases h : 0<a ∧ 4≤c
  · simp only [macroTime, macroNext, macroPair, h]
    rw [← run_eq]
    exact high_count_correct a k c h.2
  · simp only [macroTime, macroNext, macroPair, h]
    rfl

theorem macro_halts_iff (s : S) :
    (∃ n, BB6.Agent8Section.run BB6CLine.nextC n (some s) = none) ↔
    (∃ m, BB6.Agent8Section.run macroNext m (some s) = none) := by
  have h := BB6.Agent8Section.section_halts_iff_of_step
     BB6CLine.nextC (fun x : S => x) macroTime macroNext
     macro_positive (fun x => by simpa using macro_exact x) s
  exact h

#print axioms macro_positive
#print axioms macro_exact
#print axioms macro_halts_iff
end BB6.Agent46
