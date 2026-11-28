import Raw56LE17557RhoArithmetic

namespace BB6.Agent1Raw56.LE17557DefectRelation
open BB6.Agent1Raw56.LE17557RhoArithmetic

/-- Image of the finite left zero-run list under the repaired relation.
    `none` means no defect. `some j` marks the j-th zero-run (from the head),
    shortening exactly that image by eight cells. Marks beyond the finite
    list are deliberately ignored; the intended reachable invariant keeps
    them in range. -/
def imageZeros : Option Nat → List Nat → List Nat
  | _, [] => []
  | none, z :: zs => rhoZero z :: imageZeros none zs
  | some 0, z :: zs => (rhoZero z - 8) :: imageZeros none zs
  | some (j + 1), z :: zs => rhoZero z :: imageZeros (some j) zs

/-- Exact finite-zero-run relation used by the repaired left renormalization. -/
def OneDefect (mark : Option Nat) (low high : List Nat) : Prop :=
  high = imageZeros mark low

@[simp] theorem image_none_cons (z : Nat) (zs : List Nat) :
    imageZeros none (z :: zs) = rhoZero z :: imageZeros none zs := rfl

@[simp] theorem image_mark0_cons (z : Nat) (zs : List Nat) :
    imageZeros (some 0) (z :: zs) = (rhoZero z - 8) :: imageZeros none zs := rfl

@[simp] theorem image_marksucc_cons (j z : Nat) (zs : List Nat) :
    imageZeros (some (j + 1)) (z :: zs) =
      rhoZero z :: imageZeros (some j) zs := rfl

/-- Prepending a new unmarked zero-run pushes an existing mark one run deeper. -/
theorem push_unmarked (mark : Option Nat) (z : Nat) (zs : List Nat) :
    imageZeros (mark.map Nat.succ) (z :: zs) =
      rhoZero z :: imageZeros mark zs := by
  cases mark with
  | none => rfl
  | some j =>
      cases j <;> rfl

/-- Deleting an unmarked front zero-run shifts a deeper mark one run toward
    the head. -/
theorem pop_unmarked (mark : Option Nat) (z : Nat) (zs : List Nat)
    (h0 : mark ≠ some 0) :
    (imageZeros mark (z :: zs)).tail =
      imageZeros (mark.bind (fun j => if j = 0 then none else some (j - 1))) zs := by
  cases mark with
  | none => rfl
  | some j =>
      cases j with
      | zero => simp at h0
      | succ j => simp [imageZeros]

/-- A mark at the front is local: its tail is completely unmarked. -/
theorem tail_after_mark0 (z : Nat) (zs : List Nat) :
    (imageZeros (some 0) (z :: zs)).tail = imageZeros none zs := rfl

/-- Mark creation changes only the current zero-run. -/
theorem create_front (z : Nat) (zs : List Nat) :
    imageZeros (some 0) (z :: zs) =
      (rhoZero z - 8) :: imageZeros none zs := rfl

/-- Mark cancellation restores the ordinary image at the current zero-run;
    the tails of the marked and unmarked relations coincide. -/
theorem cancel_front_tail (z : Nat) (zs : List Nat) :
    (imageZeros (some 0) (z :: zs)).tail =
      (imageZeros none (z :: zs)).tail := rfl

/-- Every repaired image has the same number of finite zero-runs. -/
theorem length_image (mark : Option Nat) (zs : List Nat) :
    (imageZeros mark zs).length = zs.length := by
  induction zs generalizing mark with
  | nil => simp [imageZeros]
  | cons z zs ih =>
      cases mark with
      | none => simp [imageZeros, ih]
      | some j =>
          cases j with
          | zero => simp [imageZeros, ih]
          | succ j => simp [imageZeros, ih]

#print axioms push_unmarked
#print axioms pop_unmarked
#print axioms length_image

end BB6.Agent1Raw56.LE17557DefectRelation
