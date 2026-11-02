import Lean.Elab.Tactic.Omega
import BoundaryExtra
import CrossModelBridge

namespace BB6.CryptidBridge

/-- Independent unary pair encodings in the two authenticated raw-machine models coincide. -/
theorem pairs_eq_pat (n : Nat) : CryptidBoundary.pairs n = CryptidA.pat n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [CryptidBoundary.pairs, CryptidA.pat, ih]

/-- Convert the authentic source's A boundary to the source-verified parametric A macro input. -/
theorem preA_embed_ab (m : Nat) (ys : List Bool) :
    CryptidBoundary.preA m ys = embed (CryptidA.ab m ys) := by
  simp [CryptidBoundary.preA, CryptidA.ab, embed, pairs_eq_pat]

/-- Exact raw-step complete F-to-F return: after a zero delimiter there are
    q alternating 10 pairs, r blocks of 111, and then an explicit zero.
    All parameters and the remaining binary suffix are unrestricted. -/
theorem complete_A_pairs_triples (k q r : Nat) (ys : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
       (12*r*r+(6*((4*k+3)+q)+29)*r+2*q+2*((4*k+3)+q+4*r)+6))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.pat q ++
           (CryptidA.tblock r ++ (false::ys))))) =
    embed (CryptidA.finish (2*((4*k+3)+q+4*r)+5) ys) := by
  rw [CryptidBoundary.run_add]
  rw [CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (12*r*r+(6*((4*k+3)+q)+29)*r+2*q+2*((4*k+3)+q+4*r)+6)
    (CryptidBoundary.preA (4*k+3)
      (CryptidA.pat q ++ (CryptidA.tblock r ++ (false::ys)))) = _
  rw [preA_embed_ab]
  exact boundary_a_pairs_triples (4*k+3) q r ys

/-- Exact raw return with the zero beyond the final triple block provided
    by the implicit blank extension, rather than an explicit list element. -/
theorem complete_A_pairs_triples_nil (k q r : Nat) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
       (12*r*r+(6*((4*k+3)+q)+29)*r+2*q+2*((4*k+3)+q+4*r)+6))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.pat q ++ CryptidA.tblock r))) =
    embed (CryptidA.finish (2*((4*k+3)+q+4*r)+5) []) := by
  rw [CryptidBoundary.run_add]
  rw [CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (12*r*r+(6*((4*k+3)+q)+29)*r+2*q+2*((4*k+3)+q+4*r)+6)
    (CryptidBoundary.preA (4*k+3)
      (CryptidA.pat q ++ CryptidA.tblock r)) = _
  rw [preA_embed_ab]
  exact boundary_a_pairs_triples_nil (4*k+3) q r

#print axioms pairs_eq_pat
#print axioms preA_embed_ab
#print axioms complete_A_pairs_triples
#print axioms complete_A_pairs_triples_nil

end BB6.CryptidBridge
