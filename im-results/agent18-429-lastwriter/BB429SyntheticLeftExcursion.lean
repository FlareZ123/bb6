import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega

namespace BB429SyntheticLeftExcursion
open BB6Coverage BB429PhysicalFrontier

/-- An arbitrary prepared input at the left of a marked boundary.
This state is NOT asserted to arise from the genuine blank tape. -/
def seed : Config :=
  { state := ⟨4, by decide⟩
    head := 0
    tape := fun x => x = 1 || x = -1 || x = -2 || x = -3 }

def fatalObservation (c : Config) : Prop :=
  c.state = ⟨2, by decide⟩ ∧ c.head = 0 ∧
    c.tape c.head = false ∧ c.tape (c.head + 1) = true

theorem prepared_fatal_at_18 :
    ∃ c, run target429 18 seed = some c ∧ fatalObservation c := by
  cases h : run target429 18 seed with
  | none =>
      have hx : (run target429 18 seed).isSome = true := by decide
      simp [h] at hx
  | some c =>
      refine ⟨c,by simp,?_⟩
      have hx : (run target429 18 seed).map
          (fun x => (x.state.val, x.head, x.tape x.head, x.tape (x.head+1))) =
          some (2,0,false,true) := by decide
      rw [h] at hx
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      rcases hx with ⟨hval,hhead,h0,h1⟩
      have hstate : c.state = ⟨2, by decide⟩ := Fin.ext hval
      exact ⟨hstate,hhead,h0,h1⟩

/-- Every successful intermediate read of this prepared 18-step segment
remains strictly LEFT of the marked boundary at coordinate 1. -/
theorem prepared_stays_left :
    (List.range 19).all (fun j => decide
      (∃ c, run target429 j seed = some c ∧ c.head < 1)) = true := by decide

#print axioms prepared_fatal_at_18
#print axioms prepared_stays_left
end BB429SyntheticLeftExcursion
