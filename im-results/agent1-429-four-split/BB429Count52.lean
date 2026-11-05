import BB429Count56

namespace BB429Count52

def excludedAdditional : List Nat := [201,209,245,637]

/-- Candidate terminal residue classes modulo 8192 under the combined
    Agent33, Agent39, and Agent1 quantified rooted exclusions. -/
def live52 : List Nat :=
  BB429Count56.live56.filter (fun r => !excludedAdditional.contains r)

theorem live52_count : live52.length = 52 := by decide
theorem live52_nodup : live52.Nodup := by decide

theorem live52_iff (u : Nat) :
    u%8192 ∈ live52 ↔
      u%8192 ∈ BB429Count56.live56 ∧
      u%8192≠201 ∧ u%8192≠209 ∧
      u%8192≠245 ∧ u%8192≠637 := by
  simp [live52, excludedAdditional, List.mem_filter]

#print axioms live52_count
#print axioms live52_iff
end BB429Count52
