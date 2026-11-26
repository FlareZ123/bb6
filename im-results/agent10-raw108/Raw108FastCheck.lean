import FastAuditWeight

namespace BB6.Agent10Raw108FastCheck
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit

open BB6.Agent10ExactAuditWeight

def fastQuery (read : PartialMachine → Nat → Option Slot) (B : Nat)
    (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (read p n = some s) && (decide (p s = none) && fastWeight B p n s)

def fastCheck (read : PartialMachine → Nat → Option Slot) (B : Nat)
    (p : PartialMachine) : Audit → Bool
  | .last n s => fastQuery read B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && zipCycle p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => fastQuery read B p n s &&
      allMoves (fun mv => fastCheck read B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem fastQuery_eq (read : PartialMachine → Nat → Option Slot)
    (hr : ∀ p n, read p n = zipRead p n) (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    fastQuery read B p n s = BB6.Agent10ZipAudit.zipQueryOK B p n s := by
  simp only [fastQuery, BB6.Agent10ZipAudit.zipQueryOK, hr, fastWeight_eq]

theorem fastCheck_eq (read : PartialMachine → Nat → Option Slot)
    (hr : ∀ p n, read p n = zipRead p n) (B : Nat) (p : PartialMachine) (t : Audit) :
    fastCheck read B p t = BB6.Agent10ZipAudit.zipCheck B p t := by
  induction t generalizing p with
  | last n s => simp only [fastCheck, BB6.Agent10ZipAudit.zipCheck, fastQuery_eq read hr]
  | cycle e k r b => rfl
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    have he : (fun mv => fastCheck read B (refine p s (some mv)) (kids mv)) =
        (fun mv => BB6.Agent10ZipAudit.zipCheck B (refine p s (some mv)) (kids mv)) := by
      funext mv
      exact ih mv _
    simp only [fastCheck, BB6.Agent10ZipAudit.zipCheck, fastQuery_eq read hr, he]

theorem ordinaryCheck_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    fastCheck zipRead B p t = BB6.Agent10ZipAudit.zipCheck B p t :=
  fastCheck_eq _ (fun _ _ => rfl) B p t

theorem ordinaryQuery_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    fastQuery zipRead B p n s = BB6.Agent10ZipAudit.zipQueryOK B p n s :=
  fastQuery_eq _ (fun _ _ => rfl) B p n s

#print axioms ordinaryCheck_eq
#print axioms ordinaryQuery_eq
end BB6.Agent10Raw108FastCheck
