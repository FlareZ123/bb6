import Raw111Base

namespace BB6.Agent47Raw111
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent10ZipAudit
open BB6.Agent47PartialAudit BB6.Agent48PrefixAudit

/-- The same prefix-sharing optimization as the complete audit, with explicit
    unresolved leaves. The equality below keeps the original partial checker
    as the sole semantic trust boundary. -/
def partialAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) :
    PartialAudit → Bool
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
    rw [partialAt,partialCheck,advance_eq p t z h]
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

def partialPrefix (B : Nat) (p : PartialMachine) (a : PartialAudit) : Bool :=
  partialAt B p 0 start a

theorem partialPrefix_eq (B : Nat) (p : PartialMachine) (a : PartialAudit) :
    partialPrefix B p a = partialCheck B p a :=
  partialAt_eq B p a 0 start rfl

#print axioms partialPrefix_eq
end BB6.Agent47Raw111
