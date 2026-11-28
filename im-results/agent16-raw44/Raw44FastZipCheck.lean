import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44FastZip
open BB6Coverage BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit

/-- The finite delay set contains only delays less than six. Hence for a
sufficiently loose bound we can avoid recomputing its graph. This is the
same shortcut as Agent32's Raw59QuickWeight. -/
theorem weightOK_of_le (p : PartialMachine) (s : Slot) (n B : Nat)
    (h : n + 6 ≤ B) : weightOK p s n B = true := by
  unfold weightOK possibleDelays
  rw [List.all_eq_true]
  intro d hd
  have hd' := List.mem_range.mp (List.mem_filter.mp hd).1
  apply decide_eq_true
  omega

def quickWeight (p : PartialMachine) (s : Slot) (n B : Nat) : Bool :=
  if n + 6 ≤ B then true else weightOK p s n B

theorem quickWeight_eq (p : PartialMachine) (s : Slot) (n B : Nat) :
    quickWeight p s n B = weightOK p s n B := by
  unfold quickWeight
  split
  · exact (weightOK_of_le p s n B ‹_›).symm
  · rfl

def quickQuery (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (zipRead p n = some s) && (decide (p s = none) && quickWeight p s n B)

theorem quickQuery_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    quickQuery B p n s = zipQueryOK B p n s := by
  simp only [quickQuery, zipQueryOK, quickWeight_eq]

def fastCheck (B : Nat) (p : PartialMachine) : Audit → Bool
  | .last n s => quickQuery B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && zipCycle p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => quickQuery B p n s &&
      allMoves (fun mv => fastCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem fastCheck_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    fastCheck B p t = zipCheck B p t := by
  induction t generalizing p with
  | last n s => simp only [fastCheck,zipCheck,quickQuery_eq]
  | cycle e k r b => rfl
  | far rev d C => rfl
  | proven q h => rfl
  | split n s kids ih =>
    simp only [fastCheck,zipCheck,quickQuery_eq]
    have h : (fun mv => fastCheck B (refine p s (some mv)) (kids mv)) =
        (fun mv => zipCheck B (refine p s (some mv)) (kids mv)) := by
      funext mv
      exact ih mv _
    rw [h]

theorem fastCheck_sound {B : Nat} {p : PartialMachine} {t : Audit}
    (h : fastCheck B p t = true) : zipCheck B p t = true := by
  simpa only [fastCheck_eq] using h

#print axioms fastCheck_eq
#print axioms fastCheck_sound
end BB6.Agent16Raw44FastZip
