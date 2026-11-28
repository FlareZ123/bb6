import Q0148LowMarkerTrain
import Lean.Elab.Tactic.Omega

/-!
# Exact final-marker stack arithmetic for the q0-148 source train

This algebra identifies the final live head group and all previous
marked groups as the REVERSE of the physical right-marker parameter
list. The initial active-group height is NOT accidentally retained
as a new interior gap: it controls only the far-left countdown.
These identities are all-length, independent of termination or
simulation, and remove the last ambiguous vector-indexing point in
the proposed source boundary-to-boundary F proof.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- After any number of original source marker hops, the active
    head parameter followed by all crossed old parameters equals
    the reverse of the chronological parameter stream. -/
theorem trainEnd_active_prior (ix : HopIndex) (ns : List Nat) :
    (trainEnd ix ns).j :: (trainEnd ix ns).prior =
      (ix.j :: ns).reverse ++ ix.prior := by
  induction ns generalizing ix with
  | nil => simp [trainEnd]
  | cons n ns ih =>
      have h := ih (nextIndex ix n)
      simpa [trainEnd,nextIndex,List.reverse_cons,
        List.append_assoc] using h

/-- Repeated source marker hops are associative as a list-action:
    running two adjacent trains is literally running their union. -/
theorem trainEnd_append (ix : HopIndex) (as bs : List Nat) :
    trainEnd ix (as ++ bs) =
      trainEnd (trainEnd ix as) bs := by
  induction as generalizing ix with
  | nil => rfl
  | cons a as ih =>
      simpa [trainEnd] using ih (nextIndex ix a)

/-- Source step costs are additive under exactly the same action,
    not just asymptotically or under a bounding inequality. -/
theorem trainCost_append (ix : HopIndex) (as bs : List Nat) :
    trainCost ix (as ++ bs) =
      trainCost ix as + trainCost (trainEnd ix as) bs := by
  induction as generalizing ix with
  | nil => rfl
  | cons a as ih =>
      simpa [trainCost,trainEnd,ih,Nat.add_assoc] using
        ih (nextIndex ix a)

/-- A high source train beginning immediately AFTER the first E1
    marker has prior list EMPTY. Its final visible group parameters
    are exactly the reverse of all chronological marker parameters,
    with no spurious copy of original boundary g1. -/
theorem high_after_first_list (j first : Nat) (ns : List Nat) :
    (trainEnd (firstIndex j first) ns).j ::
      (trainEnd (firstIndex j first) ns).prior =
    (first :: ns).reverse := by
  simpa [firstIndex] using
    trainEnd_active_prior (firstIndex j first) ns

/-- The far-left height debt is exactly the initial j minus the
    number of crossed source markers, and has nothing to do with
    which interior gap parameter is currently active. -/
theorem high_after_first_far (j first : Nat) (ns : List Nat) :
    (trainEnd (firstIndex j first) ns).far =
      (j-1) - ns.length := by
  simpa [firstIndex] using
    trainEnd_far (firstIndex j first) ns

/-- The final high endpoint with a terminal short marker n=0 has
    E1 active parameter zero; its source leftmost group height is 3. -/
theorem terminal_zero_active (ix : HopIndex) (ns : List Nat) :
    (trainEnd ix (ns ++ [0])).j = 0 := by
  rw [trainEnd_append]
  rfl

/-- The final low endpoint after the two exceptional last marked
    hops has active head parameter v, and the older chronological
    parameters in exactly reversed order. -/
theorem terminal_low_order (ix : HopIndex) (ns : List Nat)
    (u v : Nat) :
    v :: u :: (trainEnd ix ns).j :: (trainEnd ix ns).prior =
      (ix.j :: ns ++ [u,v]).reverse ++ ix.prior := by
  have h := trainEnd_active_prior ix ns
  simpa [List.reverse_append,List.reverse_cons,
    List.append_assoc] using
    congrArg (fun xs : List Nat => v :: u :: xs) h

#print axioms trainEnd_active_prior
#print axioms trainEnd_append
#print axioms trainCost_append
#print axioms high_after_first_list
#print axioms high_after_first_far
#print axioms terminal_zero_active
#print axioms terminal_low_order

end BB6.Agent39Q0148Carry
