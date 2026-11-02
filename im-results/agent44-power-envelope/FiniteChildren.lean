import InverseEnumerator

namespace BB6.Agent44

/-- Every genuine positive G inverse is included in at most m+1 deterministic
candidate branches. Once these finitely many candidate children satisfy P,
all genuine children satisfy P. No metaprogramming or trusted plugin. -/
theorem affine_GAncestor_children (P : Nat → Nat → Prop)
    (b d A C t m : Nat)
    (hD : d+b/2+3=A*t+C)
    (hA : A%2^(m+1)=0)
    (hC : C%2^(m+1)≠0)
    (hcert : ∀ n, n≤m → 2≤(invAt b d n).2 →
                P (2*(invAt b d n).1-4) ((invAt b d n).2+4)) :
    ∀ k v, BB6.P1Reduction.GAncestor b d k v → 2≤v →
      P (2*k-4) (v+4) := by
  intro k v hAnc hv
  obtain ⟨n,hn,hval⟩ := affine_GAncestor_bounded b d k v A C t m hAnc hD hA hC
  have hbase := hcert n hn
  rw [hval] at hbase
  exact hbase hv

#print axioms BB6.Agent44.affine_GAncestor_children
end BB6.Agent44
