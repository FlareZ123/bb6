import CLine
import Mixed96Sound

namespace A41

/-- Audited connection between the standalone modular checker and the
    UNMODIFIED Agent 11 acceleration source. Definitional equality. -/
theorem nextC_source_equal (s : Nat × Nat × Nat) :
    nextC s = BB6CLine.nextC s := by
  rfl

theorem source_step_is_abstract_edge (s t : Nat × Nat × Nat)
    (h : BB6CLine.nextC s = some t) :
    abstractEdge (qu s) (qu t) := by
  apply real_step_is_abstract_edge s t
  rw [nextC_source_equal]
  exact h

/-- Any forward-closed predicate on the finite quotient contains every
    genuine blank-origin accelerated state. The finite-closure certificate
    must be supplied separately before concluding an unreachable cylinder. -/
theorem source_reachable_is_closed (P : Nat × Nat × Nat → Prop)
    (hinit : P (qu (5,0,1)))
    (hclosed : ∀ u v, P u → abstractEdge u v → P v)
    (s : Nat × Nat × Nat) (hr : BB6CLine.Reach s) : P (qu s) := by
  induction hr with
  | init => exact hinit
  | next x y hx hstep ih => exact hclosed (qu x) (qu y) ih (source_step_is_abstract_edge x y hstep)

#print axioms nextC_source_equal
#print axioms source_step_is_abstract_edge
#print axioms source_reachable_is_closed

end A41
