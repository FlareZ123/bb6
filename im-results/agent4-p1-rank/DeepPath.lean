import CriticalDeep
import Rank

namespace BB6.P1Deep
open BB6.Agent1
open BB6.P1Rank

private theorem iter_prepend (n a c b d e f:Nat)
    (h:T a c=some (b,d)) (hp:Iter n b d e f) :
    Iter (n+1) a c e f := by
  induction hp generalizing a c with
  | refl b d =>
    exact Iter.step 0 a c a c b d (Iter.refl a c) h
  | step n b d x y e f hp ht ih =>
    exact Iter.step (n+1) a c x y e f (ih a c h) ht

/-- Exact composition of all the inverse links into a full 2*i-step trajectory. -/
theorem corridor_path (L K i:Nat) (hK:3≤K) (hi:i≤L) :
    Iter (2*i) (left L K i) (right L K i) (left L K 0) 3 := by
  induction i with
  | zero =>
    simpa [right] using Iter.refl (left L K 0) (right L K 0)
  | succ i ih =>
    have hlink := corridor_link L K i hK (by omega)
    have hp := ih (by omega)
    have h1 := iter_prepend (2*i)
      (left L K (i+1)+3) (right L K (i+1)-2)
      (left L K i) (right L K i)
      (left L K 0) 3 hlink.2 hp
    have h2 := iter_prepend (2*i+1)
      (left L K (i+1)) (right L K (i+1))
      (left L K (i+1)+3) (right L K (i+1)-2)
      (left L K 0) 3 hlink.1 h1
    have he : 2*(i+1)=2*i+1+1 := by omega
    rw [he]
    exact h2

/-- For every L there is a genuine original P1 critical hub with an
    exact 2L-step predecessor orbit from a nonblank synthetic source.
    These existential witnesses do not assert that any source is blank-reachable. -/
theorem critical_arbitrarily_long_inverse_paths (L:Nat) :
    ∃ n a c : Nat,
      n=critIndex L ∧ 12≤a ∧ 0<c ∧
      Iter (2*L) a c (14*2^n-2*n-16) 3 := by
  let m := L+2
  let K := critWeight L
  have hK : 3≤K := crit_weight_lower L
  have hpath := corridor_path m K L hK (by omega)
  have hroot := critical_root_eq L
  have ha := (left_positive_mod m K L hK).1
  have hc := (right_odd m K L hK).1
  refine ⟨critIndex L,left m K L,right m K L,rfl,ha,by omega,?_⟩
  simpa [m,K,right,hroot] using hpath

#print axioms BB6.P1Deep.corridor_path
#print axioms BB6.P1Deep.critical_arbitrarily_long_inverse_paths
end BB6.P1Deep
