import AffineStability

namespace BB6.Agent13Affine

structure AffNode where
  m : Nat
  z : Nat
  slope : Nat

inductive ShadowReach (q side m0 z0 : Nat) : Nat → Nat → Prop where
  | root : ShadowReach q side m0 z0 m0 z0
  | step {m z m' zp : Nat}
      (hprev : ShadowReach q side m0 z0 m z)
      (hedge : ∃ t v, z=2^t*v ∧ m'=m+t+1 ∧
        2*zp+1=16*q+side+m+t+v) :
      ShadowReach q side m0 z0 m' zp

/-- The arithmetic obligations of a finite affine lift certificate.
    Only the base residue cone needs to be inspected. -/
def AffineCertificate (K q delta side : Nat)
    (nodes : List AffNode) : Prop :=
  (∀ n, n ∈ nodes → 0<n.z ∧ n.z<2^K ∧ 2^K ∣ n.slope) ∧
  (∀ n t v zp, n ∈ nodes →
    n.z=2^t*v → 2*zp+1=16*q+side+n.m+t+v →
    ∃ a n', n'∈nodes ∧ n'.m=n.m+t+1 ∧
      n'.z=zp ∧ n.slope=2^(t+1)*a ∧
      n'.slope=8*delta+a)

/-- Finite original-parameter closure plus 2-adically stable slope equations
    trap the entire shadow cone of *every* q+delta*r in the list's
    affine lift. This is a universally quantified certificate soundness theorem. -/
theorem affine_certificate_sound
    (K q delta side : Nat) (nodes : List AffNode)
    (hcert : AffineCertificate K q delta side nodes)
    (root : AffNode) (hroot : root ∈ nodes)
    (r m z : Nat)
    (hreach : ShadowReach (q+delta*r) side root.m
      (root.z+root.slope*r) m z) :
    ∃ n, n ∈ nodes ∧ n.m=m ∧ n.z+n.slope*r=z := by
  induction hreach with
  | root =>
      exact ⟨root,hroot,rfl,rfl⟩
  | @step mx zx my zy hprev hedge ih =>
      obtain ⟨n,hn,hm,hz⟩ := ih
      obtain ⟨t,v,hin,hmout,hout⟩ := hedge
      obtain ⟨hpos,hsmall,hslope⟩ := hcert.1 n hn
      have hin' : n.z+n.slope*r=2^t*v := by
        rw [hm] at *
        omega
      have hout' : 2*zy+1=16*(q+delta*r)+side+n.m+t+v := by
        rw [hm] at *
        omega
      obtain ⟨v0,a,z0,hz0,hslope0,hv,hbase,hzshift⟩ :=
        lifted_step_decompose K q delta side n.m n.z n.slope r t v zy
          hpos hsmall hslope hin' hout'
      obtain ⟨a2,n',hn',hmm,hzz,hss,hss'⟩ :=
        hcert.2 n t v0 z0 hn hz0 hbase
      refine ⟨n',hn',?_,?_⟩
      · omega
      · have haa : a2=a := by
          have hpow : 0<(2:Nat)^(t+1) := Nat.pow_pos (by decide)
          apply Nat.mul_left_cancel hpow
          calc
            2^(t+1)*a2 = n.slope := hss.symm
            _ = 2^(t+1)*a := hslope0
        rw [hzz,hss',haa]
        exact hzshift.symm

#print axioms affine_certificate_sound
end BB6.Agent13Affine
