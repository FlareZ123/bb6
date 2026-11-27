import Box28Mod5SweepSource
import Box28PairCounterSource
import Box28Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent17.Box28D2V13Residual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16WeightedSymmetry
open BB6.Agent17.Box28Symmetry
open BB6.Agent13.Box17 (decode index)

def row (i : Fin 6) : PartialMachine := fun s => some (decode ((#[#[8,24,11,13,11,13,2,23,0,6,4,20],#[8,24,11,13,11,13,2,23,0,10,4,20],#[8,20,11,13,11,13,2,23,4,0,2,21],#[8,20,11,13,11,13,2,19,4,24,0,6],#[8,20,11,13,11,13,2,19,4,24,0,10],#[8,24,11,13,11,13,2,19,2,17,4,0]] : Array (Array (Fin 25)))[i.val]![2*s.1.val+s.2.toNat]!))

theorem row0_eq : row 0 = Box28Mod5SweepSource.partialTable false := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem row0_bound (B : Nat) (m : Machine) (h : compatible (row 0) m) : WeightedBound B m := by
  apply weighted_of_never
  rw [row0_eq] at h
  exact Box28Mod5SweepSource.compatible_never false m h

theorem row1_eq : row 1 = Box28Mod5SweepSource.partialTable true := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem row1_bound (B : Nat) (m : Machine) (h : compatible (row 1) m) : WeightedBound B m := by
  apply weighted_of_never
  rw [row1_eq] at h
  exact Box28Mod5SweepSource.compatible_never true m h

theorem row2_eq : row 2 = Box28PairCounterSource.partialTable := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem row2_bound (B : Nat) (m : Machine) (h : compatible (row 2) m) : WeightedBound B m := by
  apply weighted_of_never
  rw [row2_eq] at h
  exact Box28PairCounterSource.compatible_never m h

theorem row3_rename : renamePartial ef (row 3) = row 0 := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem row3_bound (B : Nat) : ∀ m, compatible (row 3) m → WeightedBound B m :=
  weighted_cover_transport B ef (by decide) row3_rename (row0_bound B)

theorem row4_rename : renamePartial ef (row 4) = row 1 := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem row4_bound (B : Nat) : ∀ m, compatible (row 4) m → WeightedBound B m :=
  weighted_cover_transport B ef (by decide) row4_rename (row1_bound B)

theorem row5_rename : renamePartial ef (row 5) = row 2 := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem row5_bound (B : Nat) : ∀ m, compatible (row 5) m → WeightedBound B m :=
  weighted_cover_transport B ef (by decide) row5_rename (row2_bound B)

theorem rowBound (B : Nat) (i : Fin 6) (m : Machine) (hm : compatible (row i) m) : WeightedBound B m := by
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases h with h|h|h|h|h|h <;> subst i
  · exact row0_bound B m hm
  · exact row1_bound B m hm
  · exact row2_bound B m hm
  · exact row3_bound B m hm
  · exact row4_bound B m hm
  · exact row5_bound B m hm
#print axioms rowBound
end BB6.Agent17.Box28D2V13Residual
