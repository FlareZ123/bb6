import QuickWeight
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43PrefixCut
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6.Agent48PrefixAudit
open BB6Coverage.Agent31Pump BB6.Agent43QuickWeight BB6.Agent47Raw111

def fastPartialAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) : PartialAudit → Bool
  | .unresolved => true
  | .closed a => quickCheckAt B p t z a
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => quickQuery B p n s c &&
        allMoves (fun mv => fastPartialAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem fastPartialAt_eq (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) (a : PartialAudit) :
    fastPartialAt B p t z a = partialAt B p t z a := by
  induction a generalizing p t z with
  | unresolved => rfl
  | closed a => exact quickCheckAt_eq _ _ _ _ _
  | split n s kids ih =>
    rw [fastPartialAt, partialAt.eq_3]
    cases h : advance p t z n with
    | none => rfl
    | some c =>
      change (quickQuery B p n s c && allMoves (fun mv => fastPartialAt B (refine p s (some mv)) n c (kids mv))) = _
      rw [quickQuery_eq]
      apply congrArg (fun x => queryAt B p n s c && x)
      apply congrArg allMoves
      funext mv
      exact ih mv _ _ _

theorem checked_of_fastPartialAt {B : Nat} {p : PartialMachine} {t : Nat} {z : Z} {a : PartialAudit}
    (hr : zrun p t start = some z) (hc : fastPartialAt B p t z a = true) : partialCheck B p a = true := by
  rw [fastPartialAt_eq, partialAt_eq B p a t z hr] at hc
  exact hc

theorem fast_split {B : Nat} {p : PartialMachine} {t : Nat} {z : Z} {n : Nat} {s : Slot}
    {kids : Move → Audit} {c : Z}
    (ha : advance p t z n = some c) (hq : quickQuery B p n s c = true)
    (hk : ∀ mv, quickCheckAt B (refine p s (some mv)) n c (kids mv) = true) :
    quickCheckAt B p t z (.split n s kids) = true := by
  rw [quickCheckAt,ha]
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩

theorem fast_partial_split {B : Nat} {p : PartialMachine} {t : Nat} {z : Z} {n : Nat} {s : Slot}
    {kids : Move → PartialAudit} {c : Z}
    (ha : advance p t z n = some c) (hq : quickQuery B p n s c = true)
    (hk : ∀ mv, fastPartialAt B (refine p s (some mv)) n c (kids mv) = true) :
    fastPartialAt B p t z (.split n s kids) = true := by
  rw [fastPartialAt,ha]
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩

#print axioms checked_of_fastPartialAt
#print axioms fast_split
#print axioms fast_partial_split
end BB6.Agent43PrefixCut
