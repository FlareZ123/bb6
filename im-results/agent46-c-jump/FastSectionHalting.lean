import FastSectionProof
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem sec_positive (a k : Nat) : 1 ≤ secTime (a,k) := by
  simp only [secTime,exactSection]
  repeat (first | split | omega)

/-- All-input stopping equivalence between original CLine and total arithmetic two-counter section. -/
theorem section_halts_iff (a k : Nat) :
    (∃ n, BB6.Agent8Section.run BB6CLine.nextC n (some (a,k,0)) = none) ↔
      (∃ m, BB6.Agent8Section.run secNext m (some (a,k)) = none) := by
  have h := BB6.Agent8Section.section_halts_iff_of_step
    BB6CLine.nextC embed0 secTime secNext
    (fun p => by rcases p with ⟨a,k⟩; exact sec_positive a k)
    (fun p => by rcases p with ⟨a,k⟩; rw [←run_eq]; exact section_exact a k)
    (a,k)
  exact h

#print axioms sec_positive
#print axioms section_halts_iff
end BB6.Agent46
