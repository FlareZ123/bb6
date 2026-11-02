import CExclusions8
import CLine
namespace CCert

theorem published_next_agrees (s : S) : nextC s = BB6CLine.nextC s := by
  rfl

theorem source_reachable_embeds {s : S} (h : BB6CLine.Reach s) : Reach s := by
  induction h with
  | init => exact Reach.init
  | next s t _ ht ih =>
      exact Reach.step ih (by rw [published_next_agrees]; exact ht)

theorem published_reset_unreachable (j : Nat) (hj : 4 ≤ j)
    (hr : j%8=1 ∨ j%8=4 ∨ j%8=5) :
    ¬BB6CLine.Reach (2*j+1,3*j+4,0) := by
  intro h
  exact reset_unreachable j hj hr (source_reachable_embeds h)

#print axioms published_next_agrees
#print axioms published_reset_unreachable
end CCert
