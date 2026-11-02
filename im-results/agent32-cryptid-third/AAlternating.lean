import Lean.Elab.Tactic.Omega
import TenPump
import TripleIteration

namespace CryptidA

/-- Exact raw machine A-boundary return on q arbitrary 10-pairs followed
    by r triples of ones and a delimiter zero, with unrestricted suffix. -/
theorem a_pairs_triples (m q r : Nat) (ys : List Bool) :
  run (12*r*r + (6*(m+q)+29)*r + 2*q + 2*(m+q+4*r)+6)
    (ab m (pat q ++ (tblock r ++ (false::ys)))) =
  finish (2*(m+q+4*r)+5) ys := by
  have ht :
    12*r*r + (6*(m+q)+29)*r + 2*q + 2*(m+q+4*r)+6 =
      2*q + (tcost (m+q) r + (2*(m+q+4*r)+6)) := by
        simp only [tcost]
        omega
  rw [ht, run_add  (2*q) (tcost (m+q) r + (2*(m+q+4*r)+6)),
    ten_iter]
  rw [run_add (tcost (m+q) r) (2*(m+q+4*r)+6),
      iter_triplet]
  change run (2*(m+q+4*r)+6)
    (start (m+q+4*r) ys) = _
  exact close_double_zero _ _

#print axioms a_pairs_triples
end CryptidA
