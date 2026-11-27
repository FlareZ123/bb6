import PartialAudit
import ZipPrefixAudit
import CanonicalFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50PartialPrefix
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent10ZipAudit BB6.Agent48PrefixAudit
open BB6.Agent47PartialAudit BB6.Agent47CanonicalFrontier

/-- A partial audit reuses the exact already-checked execution prefix. -/
def partialAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) : PartialAudit → Bool
  | .unresolved => true
  | .closed a => checkAt B p t z a
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => queryAt B p n s c &&
        allMoves (fun mv => partialAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem partialAt_eq (B : Nat) (p : PartialMachine) (a : PartialAudit)
    (t : Nat) (z : Z) (h : zrun p t start = some z) :
    partialAt B p t z a = partialCheck B p a := by
  induction a generalizing p t z with
  | unresolved => rfl
  | closed a => exact checkAt_eq B p a t z h
  | split n s kids ih =>
    rw [partialAt,partialCheck,advance_eq p t z h n]
    cases hr : zrun p n start with
    | none => simp [zipQueryOK,zipRead,hr]
    | some c =>
      simp only [queryAt_eq B p n s c hr]
      by_cases hq : zipQueryOK B p n s = true
      · have hq' : queryAt B p n s c = true := (queryAt_eq B p n s c hr).trans hq
        have hu := queryAt_hole B p n s c hq'
        simp only [hq,Bool.true_and]
        apply congrArg allMoves
        funext mv
        exact ih mv (refine p s (some mv)) n c (refineRun p s mv hu n start c hr)
      · have hf : zipQueryOK B p n s = false := Bool.eq_false_iff.mpr hq
        simp only [hf,Bool.false_and]

def partialPrefixCheck (B : Nat) (p : PartialMachine) (a : PartialAudit) : Bool :=
  partialAt B p 0 start a

theorem partialPrefixCheck_eq (B : Nat) (p : PartialMachine) (a : PartialAudit) :
    partialPrefixCheck B p a = partialCheck B p a := partialAt_eq B p a 0 start rfl

theorem partialQuotientSound (B : Nat) (p : PartialMachine) (a : PartialAudit)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : partialPrefixCheck B p a = true) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound B m ∨
      ∃ e ∈ partialResiduals p a, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hm with ⟨e, he, hc⟩
  have hcheck : partialCheck B p a = true := (partialPrefixCheck_eq B p a).symm.trans h
  rcases partialSound B p a hf hno hcheck (renameTable e m) hc with hb | ⟨r, hr, hcompat⟩
  · have hz := firstOne_terminal p hf (renameTable e m) hc
    exact Or.inl (weighted_rename_back B e m he ((zeroNext_none_rename_iff e m he).mp hz) hb)
  · exact Or.inr ⟨r, hr, e, he, hcompat⟩

#print axioms partialAt_eq
#print axioms partialQuotientSound
end BB6.Agent50PartialPrefix
