import Agent18OneDimBridge
import BResetResidues

namespace BB6.Agent24.SourceBridge

open BusyBeaver

/-- The scalar map copied in Agent 24 is definitionally the published source-bridged Agent 18 map. -/
theorem source_G_eq (z : Nat) : BB6.OneDim.G z = BB6.Agent24.G z := rfl

theorem source_iterG_eq (n z : Nat) :
    BB6.OneDim.iterG n z = BB6.Agent24.iterG n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change BB6.OneDim.iterG n (BB6.OneDim.G z) =
      BB6.Agent24.iterG n (BB6.Agent24.G z)
    rw [source_G_eq z]
    exact ih (BB6.Agent24.G z)

/-- The syntactic reset sequence equals Agent 18's original-machine-bridged scalarA. -/
theorem source_scalarA_eq (n : Nat) :
    BB6.OneDim.scalarA n = BB6.Agent24.Reset.resetA n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change
      BB6.OneDim.iterG (BB6.OneDim.scalarA n) 0+9-
        3*(BB6.OneDim.iterG (BB6.OneDim.scalarA n) 0%2) =
      BB6.Agent24.iterG (BB6.Agent24.Reset.resetA n) 0+9-
        3*(BB6.Agent24.iterG (BB6.Agent24.Reset.resetA n) 0%2)
    rw [ih,source_iterG_eq]

/-- Reexpress original blank-tape halting of Machine B by exact residue
    classes of its recursively sampled *next* scalar reset index. -/
theorem raw_halts_iff_mod7_reset :
    IsHalt BB6.Bridge.Source.target ↔
      ∃ n : Nat, BB6.Agent24.Reset.resetA (n+1)%7=0 ∨
        BB6.Agent24.Reset.resetA (n+1)%7=6 := by
  calc
    IsHalt BB6.Bridge.Source.target ↔
        ∃ n : Nat, BB6.OneDim.iterG (BB6.OneDim.scalarA n) 0%2=0 :=
      BB6.Bridge.raw_halts_iff_two_branch
    _ ↔ ∃ n : Nat, BB6.Agent24.Reset.sampleZ n%2=0 := by
      apply exists_congr
      intro n
      change (BB6.OneDim.iterG (BB6.OneDim.scalarA n) 0)%2=0 ↔
        (BB6.Agent24.iterG (BB6.Agent24.Reset.resetA n) 0)%2=0
      rw [source_scalarA_eq n, source_iterG_eq]
    _ ↔ ∃ n : Nat, BB6.Agent24.Reset.resetA (n+1)%7=0 ∨
        BB6.Agent24.Reset.resetA (n+1)%7=6 := by
      apply exists_congr
      intro n
      exact BB6.Agent24.Reset.sample_even_iff_reset_residue n

#print axioms source_G_eq
#print axioms source_iterG_eq
#print axioms source_scalarA_eq
#print axioms raw_halts_iff_mod7_reset

end BB6.Agent24.SourceBridge
