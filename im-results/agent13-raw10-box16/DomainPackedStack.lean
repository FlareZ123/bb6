import BitPackedStack
import BoxComplement

namespace BB6.Agent13DomainPacked
open BB6Coverage BB6.Agent49Box BB6.Agent13BitPacked
open BB6.Agent1NGram (bits)

/-- A single certificate may cover a whole product of transition domains.
    At every reachable abstract configuration, every permitted transition
    must pass the same sound concrete checker. -/
def domainIndices (b : Box Slot Transition) (c : Cert) (q : Fin 6) (a : Bool) (xs : List Nat) : Bool :=
  (b (q,a)).all (fun t => indicesCheck (fun _ => some t) c q a xs)

def domainRow (b : Box Slot Transition) (c : Cert) (q : Fin 6) (a : Bool) : Bool :=
  (row c q a).valid && (row c q a).chunks.all (domainIndices b c q a)

def checkDomain (b : Box Slot Transition) (c : Cert) : Bool :=
  decide (0 < c.left.size) && decide (0 < c.right.size) &&
  (c.left.pop 0).contains (false,0) && (c.right.pop 0).contains (false,0) &&
  stateOK c 0 false 0 0 && (List.finRange 6).all (fun q => bits.all (fun a => domainRow b c q a))

theorem indices_congr (p p' : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (xs : List Nat)
    (h : p (q,a) = p' (q,a)) : indicesCheck p c q a xs = indicesCheck p' c q a xs := by
  unfold indicesCheck
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.all_cons, ih, stateStepOK, h]

theorem concreteCheck (b : Box Slot Transition) (c : Cert) (hc : checkDomain b c = true)
    (m : Machine) (hm : Fits b m) : check (fun s => some (m s)) c = true := by
  simp only [checkDomain,Bool.and_eq_true,List.all_eq_true,domainRow,domainIndices] at hc
  simp only [check,Bool.and_eq_true,List.all_eq_true,rowCheck]
  refine ⟨hc.1,?_⟩
  intro q hq a ha
  obtain ⟨hv,hi⟩ := hc.2 q hq a ha
  refine ⟨hv,?_⟩
  intro xs hxs
  have hh := hi xs hxs (m (q,a)) (hm (q,a))
  rw [indices_congr (fun s => some (m s)) (fun _ => some (m (q,a))) c q a xs rfl]
  exact hh

theorem neverDomain (b : Box Slot Transition) (c : Cert) (hc : checkDomain b c = true)
    (m : Machine) (hm : Fits b m) : NeverHalts m := by
  apply never (fun s => some (m s)) c (concreteCheck b c hc m hm) m
  intro s t h
  exact Option.some.inj h
#print axioms neverDomain
end BB6.Agent13DomainPacked
