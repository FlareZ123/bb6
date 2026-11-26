import CryptidsTapeAdapter
import BusyBeaver.Bridge

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge

def literal (xs : List Transition) : Machine :=
  fun s => xs[2*s.1.val + (if s.2 then 1 else 0)]?.getD none

/-- All ordinary transitions are fixed, while genuine halt rows are unassigned. -/
def leaf (m : Machine) : PartialMachine := fun s =>
  match m s with
  | none => none
  | some mv => some (some mv)

theorem leaf_compatible (m : Machine) : compatible (leaf m) m := by
  intro s t ht
  cases h : m s <;> simp [leaf, h] at ht ⊢
  exact ht

/-- Direct source-independent version of the ordinary-row nonhalt lifting.
    It uses only the existing exact Frontier prefix theorem. -/
theorem all_completions_never (m : Machine) (hn : NeverHalts m) :
    ∀ m', compatible (leaf m) m' → NeverHalts m' := by
  intro m' hc n
  have heq : run m n blank = run m' n blank := by
    apply common_prefix_of_partial_table (leaf m) m m' blank n
      (leaf_compatible m) hc
    intro k _ d hd
    cases hm : m (readSlot d) with
    | none =>
      have hbad := hn (k+1)
      rw [halting_entry m blank d k hd hm] at hbad
      simp at hbad
    | some mv => simp [leaf, hm]
  rw [← heq]
  exact hn n

theorem source_never (m : ConjectureMachines.Machine 6 2)
    (hn : BusyBeaver.IsNotHalt m.toBB) : NeverHalts (toAgent8 m) :=
  not_halts_to_agent8 m ((ConjectureMachines.isNotHalt_toBB_iff_not_halts m).mp hn)

#print axioms all_completions_never
#print axioms source_never
end BB6.Agent10Nov26
