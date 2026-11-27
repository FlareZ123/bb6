import PartialPrefixAudit
import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50SplitMixedPrefix
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit
open BB6.Agent47PartialAudit BB6.Agent50PartialPrefix

theorem allMoves_true {f : Move → Bool} (h : ∀ mv, f mv = true) : allMoves f = true := by
  simp [allMoves, h]

theorem partialSplit_checked {B : Nat} {p : PartialMachine} {n : Nat} {s : Slot} {kids : Move → PartialAudit}
    (hq : zipQueryOK B p n s = true)
    (hk : ∀ mv, partialPrefixCheck B (refine p s (some mv)) (kids mv) = true) :
    partialPrefixCheck B p (.split n s kids) = true := by
  rw [partialPrefixCheck_eq,partialCheck,hq]
  simp only [Bool.true_and]
  apply allMoves_true
  intro mv
  rw [← partialPrefixCheck_eq]
  exact hk mv

theorem partialClosed_checked {B : Nat} {p : PartialMachine} {a : Audit}
    (h : prefixCheck B p a = true) : partialPrefixCheck B p (.closed a) = true := by
  rw [partialPrefixCheck_eq,partialCheck,← prefixCheck_eq]
  exact h
#print axioms partialSplit_checked
#print axioms partialClosed_checked
end BB6.Agent50SplitMixedPrefix
