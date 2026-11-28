import Lean.Elab.Tactic.Omega
import BoundaryPadding
import E2UnaryTailAll

set_option maxRecDepth 8192
set_option maxHeartbeats 15000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2UnaryPhysical
open CryptidBoundary BB6.Agent31PacketSource BB6.BoundaryPadding

private theorem inputPad (k q n : Nat) :
    ObsEq
      (run n (packet (3*k+4) q 2 [false,true,true,true]))
      (run n (packet (3*k+4) q 2
        [false,true,true,true,false])) := by
  simpa [packet,word,List.append_assoc,List.replicate] using
    (source_pad n 0 1
      (packet (3*k+4) q 2 [false,true,true,true]))

/-- Physically blank-trailing packet 0 111, for arbitrary alternating
    depth q and unary k. One added explicit zero is observationally
    equivalent to the implicit infinite blank; the resulting source is
    handled by the exact 0 111 0 theorem. -/
theorem e_two_111_implicit_blank (k q : Nat) :
    ObsEq
      (run (12*k*k+49*k+68+4*q)
        (packet (3*k+4) q 2 [false,true,true,true]))
      (packet (8*k+5) 0 (2*q+6)
        [false,true,false,true,false,false]) := by
  have h := inputPad k q (12*k*k+49*k+68+4*q)
  rw [BB6.Agent37E2UnaryTail.e_two_1110 k q []] at h
  simpa only [List.append_nil] using h

/-- All lengths >=4 of the unary one-run after 0 in an E-two packet,
    with an arbitrary further suffix and exact primitive time. -/
theorem e_two_unary_long (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (packet (3*k+4) q 2
        (false :: (List.replicate (r+4) true ++ ys))) =
      packet (8*k+5) 0 (2*q+6)
        ([false,true,false,true,false,true] ++
          (List.replicate r true ++ ys)) := by
  have hr : List.replicate (r+4) true =
      [true,true,true,true] ++ List.replicate r true := by
    rw [show r+4=4+r by omega,
      ← List.replicate_append_replicate]
    rfl
  rw [hr]
  simpa only [List.cons_append,List.append_assoc,List.nil_append] using
    (BB6.Agent37E2UnaryTail.e_two_1111 k q
      (List.replicate r true ++ ys))

#print axioms e_two_111_implicit_blank
#print axioms e_two_unary_long

end BB6.Agent37E2UnaryPhysical
