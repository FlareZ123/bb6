import UniformPrecisionStep
import PredicateList

namespace BB6.Agent8Precision
open BB6.Precision
open BB6.Agent8FiniteBridge

/-- All cost-graded dyadic perturbations of a base shadow certificate. -/
def lifted (K M r : Nat) (S : Nat → Nat → Prop) (m z : Nat) : Prop :=
  ∃ z0 s, S m z0 ∧ z=z0+2^(K+M-m)*(s*r)

theorem lifted_root (K M r zbase c : Nat) (S : Nat → Nat → Prop)
    (hroot : S 0 zbase) :
    lifted K M r S 0 (zbase+2^(K+M)*(c*r)) := by
  refine ⟨zbase,c,hroot,?_⟩
  simp

theorem lifted_cost (K M r : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m≤M) :
    ∀ m z, lifted K M r S m z → m≤M := by
  intro m z ⟨z0,s,hs,_⟩
  exact hsmall m z0 hs

theorem lifted_nodiv (K M r : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m≤M)
    (hnodiv : ∀ m z, S m z → ¬2^K∣z) :
    ∀ m z, lifted K M r S m z → ¬2^K∣z := by
  intro m z ⟨z0,s,hs,hz⟩ hdiv
  have hm := hsmall m z0 hs
  have he : K≤K+M-m := by omega
  have hd : 2^K ∣ 2^(K+M-m) := Nat.pow_dvd_pow 2 he
  have hmul : 2^K ∣ 2^(K+M-m)*(s*r) := by
    rcases hd with ⟨d,hd⟩
    refine ⟨d*(s*r), ?_⟩
    rw [hd]
    ac_rfl
  have hfrom : 2^K∣z0 := by
    have hsum : 2^K∣z0+2^(K+M-m)*(s*r) := by rw [←hz]; exact hdiv
    exact (Nat.dvd_add_iff_left hmul).mpr hsum
  exact hnodiv m z0 hs hfrom

/-- An arbitrary exact lifted edge is simulated by a base edge; the
perturbation coefficient remains a natural number and cost precision decays. -/
theorem lifted_closed (K M L0 r : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m≤M)
    (hnodiv : ∀ m z, S m z → ¬2^K∣z)
    (hclosed : ∀ m z t v zp, S m z → z=2^t*v →
        2*zp+1=L0+m+t+v → S (m+t+1) zp) :
    ∀ m z t v zp, lifted K M r S m z → z=2^t*v →
    2*zp+1=(L0+16*2^(K+M)*r)+m+t+v →
    lifted K M r S (m+t+1) zp := by
  intro m z t v zp hmem hdiv hn
  obtain ⟨z0,s,hs,heq⟩ := hmem
  have hm := hsmall m z0 hs
  have hd : z0+2^(K+M-m)*(s*r)=2^t*v := by rw [←heq]; exact hdiv
  have ht := depth_lt_K K M m z0 (s*r) t v hm (hnodiv m z0 hs) hd
  have hn' : 2*zp+1=16*2^(K+M)*r+L0+m+t+v := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
  obtain ⟨v0,z0',s',hd0,hbase,hzp,hs'⟩ :=
    precision_step K M L0 r m z0 (s*r) t v zp hm ht hd hn'
  refine ⟨z0',s+8*2^(m+t+1),hclosed m z0 t v0 z0' hs hd0 hbase,?_⟩
  rw [hzp,hs']
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

#print axioms lifted_nodiv
#print axioms lifted_closed
end BB6.Agent8Precision
