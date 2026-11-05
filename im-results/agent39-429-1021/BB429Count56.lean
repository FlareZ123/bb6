import BB429Count58

namespace BB429Count56

/-- The two other whole classes already excluded by Agent39's original
eight-lift 1021-sector theorem. Neither occurs in Agent33's excluded38. -/
def additional : List Nat := [1021, 3069]

def live56 : List Nat :=
  BB429Count58.live58.filter (fun r => !additional.contains r)

theorem live56_count : live56.length = 56 := by decide

theorem live56_nodup : live56.Nodup := by
  decide

theorem live56_iff (u : Nat) :
    u%8192 ∈ live56 ↔
      u%8192 ∈ BB429Count58.live58 ∧
      u%8192 ≠ 1021 ∧ u%8192 ≠ 3069 := by
  simp [live56, additional, List.mem_filter]

#print axioms live56_count
#print axioms live56_iff

end BB429Count56
