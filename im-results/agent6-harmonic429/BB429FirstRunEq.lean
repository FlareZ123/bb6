import BB429Rank
import BB429Burst

namespace BB429FirstRunEq

/-- The original Agent 5 first-run submachine and the independently
    defined burst submachine compute exactly the same all-natural traces. -/
theorem source_first_run_eq (n : Nat) (s : BB429.State) :
    BB429.firstRun n s = BB429Burst.firstRun n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BB429.firstRun,BB429Burst.firstRun, ih]
    rfl

#print axioms source_first_run_eq
end BB429FirstRunEq
