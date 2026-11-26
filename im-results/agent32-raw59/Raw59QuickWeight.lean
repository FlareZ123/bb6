import ZipThreeHoleAudit

set_option maxHeartbeats 0

namespace BB6.Agent32Raw59QuickWeight

open BB6Coverage BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit

/-- For every candidate delay, n+6 <= B already implies the exact weighted
    inequality, since possibleDelays only enumerates delays below six. -/
theorem weightOK_of_le (p : BB6Coverage.PartialMachine) (s : Slot) (n B : Nat)
    (h : n + 6 ≤ B) : weightOK p s n B = true := by
  unfold weightOK possibleDelays
  rw [List.all_eq_true]
  intro d hd
  have hd' := List.mem_range.mp (List.mem_filter.mp hd).1
  apply decide_eq_true
  omega

/-- Exact but cheaper evaluation of the weighted part of a zip query. -/
def quickWeight (p : BB6Coverage.PartialMachine) (s : Slot) (n B : Nat) : Bool :=
  if n + 6 ≤ B then true else weightOK p s n B

theorem quickWeight_eq (p : BB6Coverage.PartialMachine) (s : Slot) (n B : Nat) :
    quickWeight p s n B = weightOK p s n B := by
  unfold quickWeight
  split
  · exact (weightOK_of_le p s n B ‹_›).symm
  · rfl

/-- A computationally cheaper query checker extensionally equal to zipQueryOK. -/
def quickZipQuery (B : Nat) (p : BB6Coverage.PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (BB6Coverage.Agent10ZipAudit.zipRead p n = some s) &&
    (decide (p s = none) && quickWeight p s n B)

theorem quickZipQuery_eq (B : Nat) (p : BB6Coverage.PartialMachine) (n : Nat) (s : Slot) :
    quickZipQuery B p n s = BB6.Agent10ZipAudit.zipQueryOK B p n s := by
  simp only [quickZipQuery, BB6.Agent10ZipAudit.zipQueryOK, quickWeight_eq]

#print axioms quickZipQuery_eq

end BB6.Agent32Raw59QuickWeight
