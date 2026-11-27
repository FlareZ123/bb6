import Lean.Elab.Tactic.Omega
import BoundaryPadding
import E2AlternatingPacket

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

namespace BB6.Agent37E2AlternatingAll

open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding BB6.Agent37E2AlternatingPacket

/-- A single arbitrary-length two-stack input, including q=0. -/
def input (k q r : Nat) (ys : List Bool) : Cfg :=
  packet (3*k+4) q 2 (longTail r ys)

/-- The q=0 and q>0 outputs differ in both their unary parameters and
    their internal bit grammars. The second alternating depth is unbounded. -/
def output (k q r : Nat) (ys : List Bool) : Cfg :=
  match q with
  | 0 => packet (8*k+3) 0 4
      (zeroTail ++ (List.replicate (2*r) true ++ ys))
  | q+1 => packet (8*k+5) 0 (2*(q+1)+2)
      (false :: List.replicate (8+2*r) true ++ ys)

/-- Exact primitive time of the prepared-state return. -/
def time (k q r : Nat) : Nat :=
  match q with
  | 0 => 12*k*k+49*k+100+4*r
  | q+1 => 12*k*k+49*k+68+4*q+4*r

theorem all_exact (k q r : Nat) (ys : List Bool) :
    run (time k q r) (input k q r ys) =
      output k q r ys := by
  cases q with
  | zero =>
      exact e_two_double_zero k r ys
  | succ q =>
      exact e_two_double_positive k q r ys

/-- The original infinite right tape treats all far-end zeros as blanks.
    Therefore, an input whose entire explicit packet tail is (01)^(r+1)
    is physically equivalent to the two-guarded input used above. -/
private theorem frontPad (k q r n : Nat) :
    ObsEq
      (run n (packet (3*k+4) q 2 (oppairs (r+1))))
      (run n (input k q r [])) := by
  simpa [input,longTail,packet,word,List.append_assoc,List.replicate]
    using (source_pad n 0 2
      (packet (3*k+4) q 2 (oppairs (r+1))))

/-- All k,q,r>=0 source-correct physical return for the prepared
    alternating tail (01)^(r+1), with no artificial terminal zeros. -/
theorem all_implicit_blank (k q r : Nat) :
    ObsEq
      (run (time k q r)
        (packet (3*k+4) q 2 (oppairs (r+1))))
      (output k q r []) := by
  have h := frontPad k q r (time k q r)
  rw [all_exact] at h
  exact h

#print axioms all_exact
#print axioms all_implicit_blank

end BB6.Agent37E2AlternatingAll
