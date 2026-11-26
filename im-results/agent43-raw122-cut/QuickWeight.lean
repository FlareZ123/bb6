import Raw122Base
set_option maxHeartbeats 0
namespace BB6.Agent43QuickWeight
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6.Agent48PrefixAudit
open BB6Coverage.Agent31Pump

theorem weightOK_of_le (p : PartialMachine) (s : Slot) (n B : Nat) (h : n+6 ≤ B) :
    weightOK p s n B = true := by
  unfold weightOK possibleDelays
  rw [List.all_eq_true]
  intro d hd
  have hd' := List.mem_range.mp (List.mem_filter.mp hd).1
  apply decide_eq_true
  omega

def quickWeight (p : PartialMachine) (s : Slot) (n B : Nat) : Bool :=
  if n+6 ≤ B then true else weightOK p s n B

theorem quickWeight_eq (p : PartialMachine) (s : Slot) (n B : Nat) :
    quickWeight p s n B = weightOK p s n B := by
  unfold quickWeight
  split
  · exact (weightOK_of_le p s n B ‹_›).symm
  · rfl

def quickZipQuery (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (zipRead p n = some s) && (decide (p s = none) && quickWeight p s n B)

theorem quickZipQuery_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    quickZipQuery B p n s = zipQueryOK B p n s := by
  simp only [quickZipQuery,zipQueryOK,quickWeight_eq]

def quickQuery (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) : Bool :=
  decide ((z.q,z.l.headD false) = s) &&
    (decide (p s = none) && quickWeight p s n B)

theorem quickQuery_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) :
    quickQuery B p n s z = queryAt B p n s z := by
  simp only [quickQuery,queryAt,quickWeight_eq]

def quickCheckAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) : (a : Audit) → Bool
  | .last n s => match advance p t z n with
    | none => false
    | some c => quickQuery B p n s c && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleAt p t z e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => quickQuery B p n s c &&
        allMoves (fun mv => quickCheckAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem quickCheckAt_eq (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) (a : Audit) :
    quickCheckAt B p t z a = checkAt B p t z a := by
  induction a generalizing p t z with
  | last n s => simp only [quickCheckAt,checkAt,quickQuery_eq]; rfl
  | cycle e k r b => rfl
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    rw [quickCheckAt,checkAt]
    cases h : advance p t z n with
    | none => rfl
    | some c =>
      change (quickQuery B p n s c && allMoves (fun mv => quickCheckAt B (refine p s (some mv)) n c (kids mv))) = _
      rw [quickQuery_eq]
      apply congrArg (fun x => queryAt B p n s c && x)
      apply congrArg allMoves
      funext mv
      exact ih mv _ _ _

def quickPrefix (B : Nat) (p : PartialMachine) (a : Audit) : Bool :=
  quickCheckAt B p 0 start a

theorem quickPrefix_eq (B : Nat) (p : PartialMachine) (a : Audit) :
    quickPrefix B p a = zipCheck B p a := by
  rw [quickPrefix,quickCheckAt_eq,checkAt_eq B p a 0 start rfl]
#print axioms quickPrefix_eq
end BB6.Agent43QuickWeight
