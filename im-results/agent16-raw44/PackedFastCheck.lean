import PackedZipAudit
import Raw44FastCanonicalCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw44Packed
open BB6Coverage BB6Coverage.Agent10ZipAudit BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent46CanonicalCut BB6.Agent46StateClosure BB6.Agent16Raw44FastZip BB6.Agent16PackedZip
def packedQuery (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (pread p n = some s) && (decide (p s = none) && quickWeight p s n B)

theorem packedQuery_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    packedQuery B p n s = zipQueryOK B p n s := by
  simp only [packedQuery, zipQueryOK, quickWeight_eq,pread_eq]

def packedCheck (B : Nat) (p : PartialMachine) : Audit → Bool
  | .last n s => packedQuery B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && pcycle p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => packedQuery B p n s &&
      allMoves (fun mv => packedCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem packedCheck_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    packedCheck B p t = zipCheck B p t := by
  induction t generalizing p with
  | last n s => simp only [packedCheck,zipCheck,packedQuery_eq]
  | cycle e k r b => simp only [packedCheck,zipCheck,pcycle_eq]
  | far rev d C => rfl
  | proven q h => rfl
  | split n s kids ih =>
    simp only [packedCheck,zipCheck,packedQuery_eq]
    have h : (fun mv => packedCheck B (refine p s (some mv)) (kids mv)) =
        (fun mv => zipCheck B (refine p s (some mv)) (kids mv)) := by
      funext mv
      exact ih mv _
    rw [h]

theorem packedCheck_sound {B : Nat} {p : PartialMachine} {t : Audit}
    (h : packedCheck B p t = true) : zipCheck B p t = true := by
  simpa only [packedCheck_eq] using h

def fast (B : Nat) (p : PartialMachine) (cut : Nat) : Cut → Bool
  | .unresolved => true
  | .closed t => packedCheck B p t
  | .bounded q C _ => tableOK p q && decide (C ≤ B)
  | .state mask => stateCheck p mask
  | .split n s kids => packedQuery B p n s &&
      allMoves (fun mv => if mv.next.val ≤ cut then
        fast B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true)
termination_by structural t => t

theorem fast_eq (B : Nat) (p : PartialMachine) (cut : Nat) (t : Cut) :
    fast B p cut t = check B p cut t := by
  induction t generalizing p cut with
  | unresolved => rfl
  | closed t => exact packedCheck_eq B p t
  | bounded q C safe => rfl
  | state mask => rfl
  | split n s kids ih =>
    simp only [fast,Agent46CanonicalCut.check,packedQuery_eq]
    have h : (fun mv => if mv.next.val ≤ cut then
          fast B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true) =
        (fun mv => if mv.next.val ≤ cut then
          check B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true) := by
      funext mv
      split <;> simp only [ih]
    rw [h]

theorem fast_sound {B : Nat} {p : PartialMachine} {cut : Nat} {t : Cut}
    (h : fast B p cut t = true) : check B p cut t = true := by
  simpa only [fast_eq] using h

theorem split_checked (B : Nat) (p : PartialMachine) (cut n : Nat) (s : Slot)
    (kids : Move → Cut) (query : packedQuery B p n s = true)
    (each : ∀ mv : Move, (if mv.next.val ≤ cut then
      check B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true) = true) :
    check B p cut (.split n s kids) = true := by
  change (zipQueryOK B p n s && allMoves (fun mv => if mv.next.val ≤ cut then
      check B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true)) = true
  rw [← packedQuery_eq,query, Bool.true_and]
  exact allMoves_of _ each

#print axioms packedQuery_eq
#print axioms packedCheck_eq
#print axioms fast_sound
#print axioms split_checked
end BB6.Agent16Raw44Packed
