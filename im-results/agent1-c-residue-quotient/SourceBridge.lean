import Quotient192
import CLine

namespace CQuotient192

/-- Definitional identity with the full unchanged repository accelerator. -/
theorem source_next_eq (s : Q) : nextC s = BB6CLine.nextC s := by
  rfl

/-- Every concrete original-source step is represented in the finite quotient. -/
theorem source_step_sound (s t : Q)
    (h : BB6CLine.nextC s = some t) :
    encode t ∈ succs (encode s) := by
  exact encode_step s t (by simpa only [source_next_eq] using h)

#print axioms source_next_eq
#print axioms source_step_sound
end CQuotient192
