import CryptidsTapeAdapter
import FrontierClose
import BusyBeaver.BB6.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH

namespace BB6.ConjectureBridge

private theorem reachable_source (m : ConjectureMachines.Machine 6 2)
    {c : ConjectureMachines.Cfg 6 2} (h : Reachable m c) :
    StateTransition.Reaches (ConjectureMachines.step m) ConjectureMachines.init c := by
  induction h with
  | root => exact Relation.ReflTransGen.refl
  | next ha hs ih => exact Relation.ReflTransGen.tail ih hs

/-- Discharges the only remaining semantic hypothesis of the tape adapter
using the *actual* Cryptids halting definition, with no extra axioms. -/
theorem not_halts_to_agent8 (m : ConjectureMachines.Machine 6 2)
    (hnot : ¬ ConjectureMachines.Halts m) :
    BB6Coverage.NeverHalts (toAgent8 m) := by
  apply reachable_live_implies_never m
  intro c hreach
  cases hs : ConjectureMachines.step m c with
  | some cfg => rfl
  | none =>
    exfalso
    apply hnot
    unfold ConjectureMachines.Halts
    rw [Part.dom_iff_mem]
    exact ⟨c, (ConjectureMachines.mem_eval').mpr ⟨reachable_source m hreach, hs⟩⟩

end BB6.ConjectureBridge

namespace BB6.F287

open BB6.ConjectureBridge BB6Coverage

/-- Exactly the pinned A6 source machine, whose RLE text is
1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---. -/
def source : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.machine

def original : BB6Coverage.Machine := toAgent8 source

/-- Literal external RLE transition table, preserving its blank-state label and
halt at F/1. Used to prevent a silent state-permutation or text mismatch. -/
def expectedRLE (s : Slot) : Transition :=
  match s.1.val, s.2 with
  | 0, false => some ⟨true,  true,  1⟩
  | 0, true  => some ⟨false, false, 5⟩
  | 1, false => some ⟨true,  true,  2⟩
  | 1, true  => some ⟨false, true,  0⟩
  | 2, false => some ⟨true,  false, 3⟩
  | 2, true  => some ⟨false, true,  1⟩
  | 3, false => some ⟨false, false, 4⟩
  | 3, true  => some ⟨false, false, 2⟩
  | 4, false => some ⟨false, false, 0⟩
  | 4, true  => some ⟨false, false, 2⟩
  | 5, false => some ⟨false, false, 1⟩
  | 5, true  => none
  | _, _ => none

/-- All twelve source transitions are definitionally the specified RLE
tokens, including the halting convention. -/
theorem original_eq_expectedRLE : original = expectedRLE := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem original_never : NeverHalts original :=
  not_halts_to_agent8 source
    BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.not_halts

def rootCylinder : PartialMachine := fun s => some (original s)

/-- Authentic, source-identified A6/F287 original-root nonhalting leaf. -/
theorem root_cover (bound : Nat) : Cover (DecidedBelow bound) rootCylinder := by
  apply Cover.leaf
  intro m hm
  have heq : m = original := by
    funext slot
    exact hm slot (original slot) rfl
  rw [heq]
  exact Or.inl original_never

/-- A singleton leaf compatible with the global disjoint-frontier audit. -/
def rootedAudit (bound : Nat) : FrontierAudit (DecidedBelow bound) rootCylinder :=
  .certified rootCylinder (root_cover bound)

#print axioms BB6.ConjectureBridge.not_halts_to_agent8
#print axioms original_eq_expectedRLE
#print axioms original_never
#print axioms root_cover
end BB6.F287
