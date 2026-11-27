import PartialPrefixAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50QuickPrefix
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent10ZipAudit BB6.Agent48PrefixAudit
open BB6.Agent47PartialAudit BB6.Agent50PartialPrefix BB6.Agent47CanonicalFrontier

-- Same exact short-weight reduction as Agent10's FastAuditWeight.lean;
-- isolated here to avoid importing the unrelated reweighting theorem closure.
theorem weight_short (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : n+6 ≤ B) : weightOK p s n B = true := by
  unfold weightOK
  apply List.all_eq_true.mpr
  intro d hd
  unfold possibleDelays at hd
  have hd6 := List.mem_range.mp (List.mem_filter.mp hd).1
  exact decide_eq_true (by omega)

def quickWeight (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  if n+6 ≤ B then true else weightOK p s n B

theorem quickWeight_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    quickWeight B p n s = weightOK p s n B := by
  unfold quickWeight
  split
  · exact (weight_short B p n s ‹_›).symm
  · rfl

def quickQuery (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) : Bool :=
  decide ((z.q,z.l.headD false) = s) && (decide (p s = none) && quickWeight B p n s)

theorem quickQuery_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) :
    quickQuery B p n s z = queryAt B p n s z := by
  simp only [quickQuery,queryAt,quickWeight_eq]

def quickAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) : Audit → Bool
  | .last n s => match advance p t z n with
    | none => false
    | some c => quickQuery B p n s c && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleAt p t z e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => quickQuery B p n s c &&
        allMoves (fun mv => quickAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem quickAt_eq (B : Nat) (p : PartialMachine) (a : Audit) (t : Nat) (z : Z) :
    quickAt B p t z a = checkAt B p t z a := by
  induction a generalizing p t z with
  | last n s =>
    cases h : advance p t z n <;> simp only [quickAt,checkAt,h,quickQuery_eq]
  | cycle e k r b => rfl
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    cases h : advance p t z n with
    | none => simp only [quickAt,checkAt,h]
    | some c =>
      simp only [quickAt,checkAt,h,quickQuery_eq]
      congr 1
      apply congrArg allMoves
      funext mv
      exact ih mv _ _ _

def quickPartialAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) : PartialAudit → Bool
  | .unresolved => true
  | .closed a => quickAt B p t z a
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => quickQuery B p n s c &&
        allMoves (fun mv => quickPartialAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem quickPartialAt_eq (B : Nat) (p : PartialMachine) (a : PartialAudit) (t : Nat) (z : Z) :
    quickPartialAt B p t z a = partialAt B p t z a := by
  induction a generalizing p t z with
  | unresolved => rfl
  | closed a => exact quickAt_eq B p a t z
  | split n s kids ih =>
    cases h : advance p t z n with
    | none => simp only [quickPartialAt,partialAt,h]
    | some c =>
      simp only [quickPartialAt,partialAt,h,quickQuery_eq]
      congr 1
      apply congrArg allMoves
      funext mv
      exact ih mv _ _ _

def quickCheck (B : Nat) (p : PartialMachine) (a : Audit) : Bool := quickAt B p 0 start a

def quickPartialCheck (B : Nat) (p : PartialMachine) (a : PartialAudit) : Bool := quickPartialAt B p 0 start a

theorem quickCheck_eq (B : Nat) (p : PartialMachine) (a : Audit) : quickCheck B p a = prefixCheck B p a := quickAt_eq B p a 0 start

theorem quickPartialCheck_eq (B : Nat) (p : PartialMachine) (a : PartialAudit) : quickPartialCheck B p a = partialPrefixCheck B p a := quickPartialAt_eq B p a 0 start

#print axioms quickCheck_eq
#print axioms quickPartialCheck_eq
end BB6.Agent50QuickPrefix
