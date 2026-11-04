import FastParents
import ClosedCert

namespace CascadeResetInverse

def fastCheckChunk (s part:List Nat):Bool :=
  part.all (fun u => (fastParents u).all (fun h => s.contains h))

def fastClosedCert (s:List Nat):Bool := fastCheckChunk s s

/-- If every disjoint or overlapping chunk is reverse-closed in the
    common universe, their concatenation is a sound finite certificate. -/
theorem fastClosedCert_of_chunks (chunks:List (List Nat))
    (hc:∀ c, c∈chunks → fastCheckChunk chunks.flatten c=true):
    fastClosedCert chunks.flatten=true := by
  apply List.all_eq_true.mpr
  intro u hu
  obtain ⟨c,hc1,huc⟩ := List.mem_flatten.mp hu
  exact (List.all_eq_true.mp (hc c hc1)) u huc

theorem fastClosedCert_implies_old (s:List Nat)
    (hc:fastClosedCert s=true):closedCert s=true := by
  apply List.all_eq_true.mpr
  intro u hu
  apply List.all_eq_true.mpr
  intro h hh
  exact (List.all_eq_true.mp ((List.all_eq_true.mp hc) u hu)) h
    ((fastParents_iff h u).mpr ((parents_iff h u).mp hh))

/-- Converts the faster finite Boolean cone checks back into the already
    source-certified root reachability obstruction, without new axioms. -/
theorem fastClosedCert_excludes (s:List Nat) (u:Nat)
    (hc:fastClosedCert s=true) (hm:u∈s) (hnot:2∉s) :
    ¬CascadeSweep.ReachC (2,0) (u,0) :=
  closedCert_excludes s u (fastClosedCert_implies_old s hc) hm hnot

#print axioms fastClosedCert_of_chunks
#print axioms fastClosedCert_implies_old
#print axioms fastClosedCert_excludes
end CascadeResetInverse
