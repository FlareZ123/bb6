import RayFinite
import FrontierMass

namespace BB6Coverage

/-- Physically marked return followed by a fresh opposite ray.
    A/0 writes 1 and visits q. Both q/0 and q/1 move against A's
    initial direction and stay in q. They may write either bit.
    All other nine instructions remain unassigned. -/
def markedReturnTable (q : Fin 6) (dir write0 write1 : Bool) : PartialMachine :=
  fun slot =>
    if slot = initialSlot then some (some ⟨true, dir, q⟩)
    else if slot = (q, false) then some (some ⟨write0, !dir, q⟩)
    else if slot = (q, true) then some (some ⟨write1, !dir, q⟩)
    else none

/-- B..F, both initial directions, and both arbitrary write bits
    at each of the two q inputs: 5 * 2 * 2 * 2 = 40 cases. -/
def markedReturnParams : List (Fin 6 × Bool × Bool × Bool) :=
  ((List.finRange 6).filter (fun q => q != 0)).flatMap (fun q =>
    [true, false].flatMap (fun dir =>
      [true, false].flatMap (fun w0 =>
        [true, false].map (fun w1 => (q, dir, w0, w1)))))

def markedReturnCases : List PartialMachine :=
  markedReturnParams.map (fun (q, dir, w0, w1) =>
    markedReturnTable q dir w0 w1)

theorem markedReturnParams_length : markedReturnParams.length = 40 := by decide
theorem markedReturnParams_nodup : markedReturnParams.Nodup := by decide

/-- The original finite-support source checker executes the exact
    three-move blank prefix, including the marked read-one input,
    then proves the all-time blank left/right ray. -/
theorem markedReturnParams_ray :
    markedReturnParams.all (fun (q, dir, w0, w1) =>
      finiteRayCheck (markedReturnTable q dir w0 w1)
        3 (!dir) (fun s => s == q)) = true := by
  decide

theorem markedReturn_source_cover (q : Fin 6) (dir w0 w1 : Bool)
    (h : (q, dir, w0, w1) ∈ markedReturnParams) (bound : Nat) :
    Cover (DecidedBelow bound) (markedReturnTable q dir w0 w1) := by
  exact finiteRayCheck_sound (markedReturnTable q dir w0 w1)
    3 (!dir) (fun s => s == q) bound
    ((List.all_eq_true.mp markedReturnParams_ray) _ h)

/-- Each certificate fixes precisely A/0, q/0 and q/1. -/
theorem markedReturnCases_mass :
    markedReturnCases.all (fun p => decide (cylinderMass p = 25^9)) = true := by
  decide

theorem markedReturnCase_mass (p : PartialMachine)
    (h : p ∈ markedReturnCases) :
    cylinderMass p = 25^9 :=
  of_decide_eq_true ((List.all_eq_true.mp markedReturnCases_mass) p h)

/-- Two distinct parameter tuples cannot describe compatible
    cylinders. A/0 determines q and dir; q/0 and q/1 then determine
    their independent write bits. -/
theorem markedReturn_unique (m : Machine) (q q' : Fin 6)
    (dir dir' w0 w0' w1 w1' : Bool)
    (hq : q ≠ 0) (_hq' : q' ≠ 0)
    (h : compatible (markedReturnTable q dir w0 w1) m)
    (h' : compatible (markedReturnTable q' dir' w0' w1') m) :
    (q, dir, w0, w1) = (q', dir', w0', w1') := by
  have hA : m initialSlot = some ⟨true, dir, q⟩ :=
    h initialSlot _ (by simp [markedReturnTable])
  have hA' : m initialSlot = some ⟨true, dir', q'⟩ :=
    h' initialSlot _ (by simp [markedReturnTable])
  have heq : (⟨true, dir, q⟩ : Move) = ⟨true, dir', q'⟩ :=
    Option.some.inj (hA.symm.trans hA')
  have hdir : dir = dir' := congrArg Move.right heq
  have hstate : q = q' := congrArg Move.next heq
  subst dir'
  subst q'
  have hs0 : (q, false) ≠ initialSlot := by
    simp [initialSlot, hq]
  have hs1 : (q, true) ≠ initialSlot := by
    simp [initialSlot]
  have h0 : m (q, false) = some ⟨w0, !dir, q⟩ :=
    h (q, false) _ (by simp [markedReturnTable, hs0])
  have h0' : m (q, false) = some ⟨w0', !dir, q⟩ :=
    h' (q, false) _ (by simp [markedReturnTable, hs0])
  have hw0 : w0 = w0' :=
    congrArg Move.write (Option.some.inj (h0.symm.trans h0'))
  have h1 : m (q, true) = some ⟨w1, !dir, q⟩ :=
    h (q, true) _ (by simp [markedReturnTable, hs1])
  have h1' : m (q, true) = some ⟨w1', !dir, q⟩ :=
    h' (q, true) _ (by simp [markedReturnTable, hs1])
  have hw1 : w1 = w1' :=
    congrArg Move.write (Option.some.inj (h1.symm.trans h1'))
  simp [hw0, hw1]

#print axioms markedReturnParams_ray
#print axioms markedReturn_source_cover
#print axioms markedReturnCases_mass
#print axioms markedReturn_unique

end BB6Coverage
