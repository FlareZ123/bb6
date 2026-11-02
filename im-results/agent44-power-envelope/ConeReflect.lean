import ConeKernel
import FiniteChildren

namespace BB6.Agent44

/-- Single original-source proof constructor: an affine inverse node reduces
to at most m+1 finite Blocked child certificates, provided its exceptional
input and one shifted-coordinate valuation are excluded. -/
theorem blocked_from_val_cert (b d A C t m : Nat)
    (hb : 8≤b) (hmod : b%4=0) (hd : 0<d)
    (hno : ∀ k, ¬BB6.P1Reduction.GAncestor b d k 1)
    (hD : d+b/2+3=A*t+C)
    (hA : A%2^(m+1)=0)
    (hC : C%2^(m+1)≠0)
    (hcert : ∀ n, n≤m → 2≤(invAt b d n).2 →
                BB6.Agent4Cone.Blocked (2*(invAt b d n).1-4)
                    ((invAt b d n).2+4)) :
    BB6.Agent4Cone.Blocked b d := by
  exact BB6.Agent4Cone.Blocked.feeder b d hb hmod hd hno
    (affine_GAncestor_children BB6.Agent4Cone.Blocked b d A C t m hD hA hC hcert)

/-- Compose the reflected finite certificate with Agent 4's universally
proved Blocked soundness, obtaining a genuine blank-reachability exclusion. -/
theorem no_reach_from_val_cert (b d A C t m : Nat)
    (hb : 8≤b) (hmod : b%4=0) (hd : 0<d)
    (hno : ∀ k, ¬BB6.P1Reduction.GAncestor b d k 1)
    (hD : d+b/2+3=A*t+C)
    (hA : A%2^(m+1)=0)
    (hC : C%2^(m+1)≠0)
    (hcert : ∀ n, n≤m → 2≤(invAt b d n).2 →
                BB6.Agent4Cone.Blocked (2*(invAt b d n).1-4)
                    ((invAt b d n).2+4)) :
    ¬BB6.Agent1.Reach b d := by
  exact BB6.Agent4Cone.blocked_no_reach b d
    (blocked_from_val_cert b d A C t m hb hmod hd hno hD hA hC hcert)

#print axioms BB6.Agent44.blocked_from_val_cert
#print axioms BB6.Agent44.no_reach_from_val_cert
end BB6.Agent44
