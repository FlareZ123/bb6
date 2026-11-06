import UniformPrecisionStep
namespace BB6.Precision

/-- Exact dyadic scalar inverse reachability from a specified root. -/
inductive ShadowReach (L root : Nat) : Nat → Nat → Prop where
| root : ShadowReach L root 0 root
| step {m z} : ShadowReach L root m z →
    (t v zp : Nat) → z=2^t*v →
    2*zp+1=L+m+t+v →
    ShadowReach L root (m+t+1) zp

/-- For every perturbation r, all finite scalar inverse paths from the
    perturbed root are simulated by the base closed shadow graph, retaining
    precision 2^(K+M-m). No depth or step-count cutoff appears. -/
theorem uniform_shadow_lift (K M L0 zbase r c : Nat)
    (S : Nat → Nat → Prop)
    (hroot : S 0 zbase)
    (hsmall : ∀ m z, S m z → m≤M)
    (hnodiv : ∀ m z, S m z → ¬2^K ∣ z)
    (hclosed : ∀ m z t v zp, S m z → z=2^t*v →
        2*zp+1=L0+m+t+v → S (m+t+1) zp)
    (m z : Nat)
    (hpath : ShadowReach (L0+16*2^(K+M)*r)
          (zbase+2^(K+M)*(c*r)) m z) :
    ∃ z0 s, S m z0 ∧ z=z0+2^(K+M-m)*s := by
  induction hpath with
  | root =>
      refine ⟨zbase,c*r,hroot,?_⟩
      simp
  | @step m z hh t v zp hdiv hn ih =>
      rcases ih with ⟨z0,s,hs,heq⟩
      have hm := hsmall m z0 hs
      have hdiv' : z0+2^(K+M-m)*s=2^t*v := by
        rw [←heq]
        exact hdiv
      have ht := depth_lt_K K M m z0 s t v hm
          (hnodiv m z0 hs) hdiv'
      have hn' : 2*zp+1=16*2^(K+M)*r+L0+m+t+v := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
      rcases precision_step K M L0 r m z0 s t v zp hm ht hdiv' hn'
          with ⟨v0,z0',s',hv0,hbase,hzp,hs'⟩
      exact ⟨z0',s',hclosed m z0 t v0 z0' hs hv0 hbase,hzp⟩

#print axioms uniform_shadow_lift
end BB6.Precision
