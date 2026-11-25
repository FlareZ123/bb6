import Raw10BoxBridge
import TranslatedCycler

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10Box8
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49BoxBridge
open BB6.Agent50TranslatedCycler

/-- A root-refining two-hole cylinder in the raw10 parent. It fixes exactly
    the ten slots visited by the lasso (including F0=code 10, or 0RC), and
    leaves B1 and F1 unassigned. -/
def table : PartialMachine :=
  fun s =>
    if s = (1,true) then none
    else if s = (5,false) then some (some ⟨false,true,2⟩)
    else held s

/-- The default completion halts at the two still-unknown B1 and F1 rows.
    The checked 24+14-step trace never reads either row. -/
def default : Machine := weightedTNFDefaultCompletion table

theorem cycle_check : translatedCyclerCheckRight default 24 14 7 = true := by
  decide

theorem default_never : NeverHalts default :=
  translatedCyclerCheckRight_sound cycle_check

/-- A finite exact recurrence of the default completion gives an infinite
    sparse knownRun, hence transfers to every total completion of table. -/
theorem known_forever : weightedTNFKnownRunForever table := by
  intro n
  have hrun : (run default n blank).isSome = true := default_never n
  have hknown : (knownRun table n).isSome = true := by
    rw [weightedTNFKnownRun_eq_defaultRun table n]
    exact hrun
  cases h : knownRun table n with
  | none => simp [h] at hknown
  | some c => exact ⟨c,rfl⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  weightedTNFKnownRunForever_sound table known_forever m hm

theorem root : table initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem support : TNFSupport table 6 := by
  intro s t hs
  exact ⟨s.1.isLt, fun mv hm => mv.next.isLt⟩

theorem no_assigned_halt : weightedTNFNoAssignedHalt table := by
  decide

/-- A proof-carrying score-B TNF leaf for all 625 B1/F1 completions. -/
def certificate (B : Nat) : WeightedTNFCertificate B table 6 :=
  .nonhalt root support no_assigned_halt never

def cover (B : Nat) : Cover (WeightedBound B) table :=
  (certificate B).toCover

#print axioms cycle_check
#print axioms default_never
#print axioms known_forever
#print axioms never
#print axioms certificate
#print axioms cover
end BB6.Agent50Raw10Box8
