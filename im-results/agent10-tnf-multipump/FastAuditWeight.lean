import ExactAuditWeight
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10ExactAuditWeight
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

/-- A query with at least five spare blank-delay moves needs no enumeration. -/
theorem weightOK_of_short (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : n + 6 ≤ B) : weightOK p s n B = true := by
  unfold weightOK
  apply List.all_eq_true.mpr
  intro d hd
  unfold possibleDelays at hd
  have hd6 := List.mem_range.mp (List.mem_filter.mp hd).1
  exact decide_eq_true (by omega)

def fastWeight (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  if n + 6 ≤ B then true else weightOK p s n B

theorem fastWeight_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    fastWeight B p n s = weightOK p s n B := by
  unfold fastWeight
  split
  · exact (weightOK_of_short B p n s ‹_›).symm
  · rfl

/-- Only scores within five of the proposed cutoff enumerate predecessor paths. -/
def fastWeightCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => fastWeight B p n s
  | .cycle .. => true
  | .far .. => true
  | .proven .. => true
  | .split n s kids => fastWeight B p n s &&
      allMoves (fun mv => fastWeightCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem fastWeightCheck_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    fastWeightCheck B p t = weightCheck B p t := by
  induction t generalizing p with
  | last n s => exact fastWeight_eq B p n s
  | cycle e k r b => rfl
  | far rev d cert => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    have he : (fun mv => fastWeightCheck B (refine p s (some mv)) (kids mv)) =
        (fun mv => weightCheck B (refine p s (some mv)) (kids mv)) := by
      funext mv
      exact ih mv _
    simp only [fastWeightCheck,weightCheck,fastWeight_eq,he]

#print axioms fastWeightCheck_eq
end BB6.Agent10ExactAuditWeight
