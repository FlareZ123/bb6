import Raw10BoxCore
import BlockFARBridge
import WeightedFirstOneCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Raw10BoxFar

open BB6Coverage
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent13BlankDelay

/-- The strongest partial table forced by a product box: retain exactly the
    singleton ordinary-move domains; leave every other slot unspecified. A
    singleton halt is also left unspecified, making the projection weaker. -/
def singletonProjection (box : Box Slot Transition) : PartialMachine :=
  fun s =>
    match box s with
    | [some mv] => some (some mv)
    | _ => none

/-- Convert the singleton projection into the primitive BlockFAR table. -/
def tableOfBox (box : Box Slot Transition) : BB6BlockFAR.Table :=
  fun q sym =>
    match box (q, sym) with
    | [some mv] => some ⟨mv.write, mv.right, mv.next⟩
    | _ => none

/-- Every completion fitting a box extends its singleton projection. -/
theorem fits_singletonProjection (box : Box Slot Transition)
    (m : Machine) (hm : Fits box m) :
    compatible (singletonProjection box) m := by
  intro s t ht
  have hs := hm s
  unfold singletonProjection at ht
  cases hb : box s with
  | nil =>
      simp [hb] at ht
  | cons a tail =>
      cases tail with
      | nil =>
          cases a with
          | none =>
              simp [hb] at ht
          | some mv =>
              simp [hb] at ht
              subst t
              simpa [hb] using hs
      | cons b tail' =>
          simp [hb] at ht

/-- The BlockFAR bridge of the table is exactly the singleton projection. -/
theorem partialTable_tableOfBox (box : Box Slot Transition) :
    BB6BlockFAR.partialTable (tableOfBox box) = singletonProjection box := by
  funext s
  rcases s with ⟨q, sym⟩
  cases hb : box (q, sym) with
  | nil =>
      simp [tableOfBox, singletonProjection, BB6BlockFAR.partialTable, hb]
  | cons a tail =>
      cases tail with
      | nil =>
          cases a with
          | none =>
              simp [tableOfBox, singletonProjection, BB6BlockFAR.partialTable, hb]
          | some mv =>
              cases mv
              simp [tableOfBox, singletonProjection, BB6BlockFAR.partialTable,
                BB6BlockFAR.sourceMove, hb]
      | cons b tail' =>
          simp [tableOfBox, singletonProjection, BB6BlockFAR.partialTable, hb]

/-- A BlockFAR certificate for a singleton projection proves every completion
    of the entire product box nonhalting in the original BB6Coverage semantics. -/
theorem box_never_of_valid {d n : Nat} (cert : BB6BlockFAR.Data d n)
    (box : Box Slot Transition)
    (hValid : cert.Valid (tableOfBox box))
    (m : Machine) (hm : Fits box m) :
    NeverHalts m := by
  apply BB6BlockFAR.transfer_never (tableOfBox box) m
  · rw [partialTable_tableOfBox]
    exact fits_singletonProjection box m hm
  · exact cert.sound (tableOfBox box) hValid

/-- The same box certificate supplies the existing weighted score predicate;
    no change to the blank-delay or final-query convention is made. -/
theorem box_weighted_of_valid (B : Nat) {d n : Nat}
    (cert : BB6BlockFAR.Data d n) (box : Box Slot Transition)
    (hValid : cert.Valid (tableOfBox box)) :
    ∀ m, Fits box m → WeightedBound B m := by
  intro m hm
  exact weighted_of_never B m (box_never_of_valid cert box hValid m hm)

#print axioms fits_singletonProjection
#print axioms partialTable_tableOfBox
#print axioms box_never_of_valid
#print axioms box_weighted_of_valid

end BB6.Agent17Raw10BoxFar
