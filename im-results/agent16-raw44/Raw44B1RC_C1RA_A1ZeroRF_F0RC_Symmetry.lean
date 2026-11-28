import Raw44B1RC_C1RA_A1ZeroRE_F0RC_Growth
import WeightedSymmetry\nimport WeightedTNF

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44C1RA_A1ZeroRF_F0RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16WeightedSymmetry

/-!
E/F-renaming of the 6n+12 Raw44 1RA A1=0RE, F0=0RC growth theorem.
The missing E0 becomes an arbitrary missing F0 transition.
-/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true  => some (some ⟨false,true,0⟩)
  | 5,true  => some (some ⟨false,true,4⟩)
  | _,_ => none

private abbrev ef : StatePerm := swapStates (4 : Fin 6) 5

theorem renamed_table :
    renamePartial ef table = BB6.Agent16Raw44C1RA_A1ZeroRE_F0RC.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [renamePartial, ef, swapStates, renameMove, table, BB6.Agent16Raw44C1RA_A1ZeroRE_F0RC.table]

private theorem rename_never_back (e : StatePerm) (hroot : e.forward (0 : Fin 6) = 0)
    (m : Machine) (h : NeverHalts (renameTable e m)) : NeverHalts m := by
  intro n
  have hrun : run (renameTable e m) n blank =
      (run m n blank).map (renameConfig e) := by
    simpa [renameConfig,blank,hroot] using rename_run e m blank n
  have hn := h n
  rw [hrun] at hn
  cases hr : run m n blank with
  | none => simp [hr] at hn
  | some d => simp [hr]

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have hc := rename_compatible ef hm
  rw [renamed_table] at hc
  have hn := BB6.Agent16Raw44C1RA_A1ZeroRE_F0RC.never (renameTable ef m) hc
  exact rename_never_back ef (by simp [ef, swapStates]) m hn

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms renamed_table
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44C1RA_A1ZeroRF_F0RC
