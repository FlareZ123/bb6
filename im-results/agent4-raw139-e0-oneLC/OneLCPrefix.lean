import OneLCHybrid
import ZipPrefixAudit
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4OneLCPrefix
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent4OneLCHybrid BB6.Agent48PrefixAudit

def checkAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) : Branch B → Bool
  | .closed a => BB6.Agent48PrefixAudit.checkAt B p t z a
  | .b2 f _ _ c => block2OK (if f then reflectPartial p else p) c
  | .b3 f _ _ c => block3OK (if f then reflectPartial p else p) c
  | .b4 f _ _ c => block4OK (if f then reflectPartial p else p) c
  | .covered q _ => tableOK p q
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => queryAt B p n s c && allMoves (fun mv => checkAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem checkAt_eq (B : Nat) (p : PartialMachine) (a : Branch B)
    (t : Nat) (z : Z) (h : zrun p t BB6Coverage.Agent31Pump.start = some z) :
    checkAt B p t z a = BB6.Agent4OneLCHybrid.check B p a := by
  induction a generalizing p t z with
  | closed a => exact BB6.Agent48PrefixAudit.checkAt_eq B p a t z h
  | b2 f d n c => rfl
  | b3 f d n c => rfl
  | b4 f d n c => rfl
  | covered q safe => rfl
  | split n s kids ih =>
    rw [checkAt,BB6.Agent4OneLCHybrid.check,advance_eq p t z h]
    cases hr : zrun p n BB6Coverage.Agent31Pump.start with
    | none => simp [zipQueryOK,zipRead,hr]
    | some c =>
      simp only [queryAt_eq B p n s c hr]
      by_cases hq : zipQueryOK B p n s = true
      · have hq' : queryAt B p n s c = true := (queryAt_eq B p n s c hr).trans hq
        have hu := queryAt_hole B p n s c hq'
        simp only [hq,Bool.true_and]
        apply congrArg allMoves
        funext mv
        exact ih mv (refine p s (some mv)) n c (refineRun p s mv hu n BB6Coverage.Agent31Pump.start c hr)
      · have hf : zipQueryOK B p n s = false := Bool.eq_false_iff.mpr hq
        simp only [hf,Bool.false_and]

def checkPrefix (B : Nat) (p : PartialMachine) (a : Branch B) : Bool :=
  checkAt B p 0 BB6Coverage.Agent31Pump.start a

theorem checkPrefix_eq (B : Nat) (p : PartialMachine) (a : Branch B) :
    checkPrefix B p a = BB6.Agent4OneLCHybrid.check B p a := checkAt_eq B p a 0 _ rfl

theorem soundPrefix (B : Nat) (p : PartialMachine) (a : Branch B)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p) (h : checkPrefix B p a = true) : Cover (WeightedBound B) p :=
    BB6.Agent4OneLCHybrid.sound B p a hf hn ((checkPrefix_eq B p a).symm.trans h)
#print axioms soundPrefix
end BB6.Agent4OneLCPrefix
