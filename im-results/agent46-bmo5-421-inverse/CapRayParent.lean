import CapTerminalInverse

namespace CapSieve

/-- The exact range of the relaxed positive exit. -/
def ExitP (k p : Nat) : Prop :=
  2≤p ∧ p≤2*P (k+1)-2 ∧ p%2=(k+1)%2 ∧ p%3=2^(k+1)%3

theorem positive_next_range {k q : Nat} (h : PosQ k q) :
    ExitP k (positiveNext k q) := by
  have hp : 0<q := by have := h.1; omega
  have hb := positive_next_bounds hp h.2.1
  exact ⟨hb.1,hb.2,positive_next_parity hp h.2.1 h.2.2,positive_next_phase h⟩

def rayParent (k p : Nat) : Nat := reduceRay k ((p+2*P k-3)/3)

/-- Every admissible relaxed exit has exactly one canonical parent for k>=1. -/
theorem ray_parent_spec {k p : Nat} (hk : 1≤k) (hp : ExitP k p) :
    CanonQ k (rayParent k p) ∧ positiveNext k (rayParent k p)=p := by
  let U := p+2*P k-3
  have hP := p_ge k
  have hUeq : U+3=p+2*P k := by dsimp [U]; omega
  have hUlo : 2*P k-1≤U := by have := hp.1; omega
  have hUhi : U≤6*P k-5 := by
    have hh := hp.2.1
    rw [p_succ] at hh
    omega
  have hUdiv : U%3=0 := by
    have hh := hp.2.2.2
    rw [Nat.pow_succ] at hh
    unfold P at hUeq
    omega
  have hmul : 3*(U/3)=U := by omega
  have hqlo : k+6≤U/3 := by
    by_cases h : 2≤k
    · have hscale := band_scale_lower h
      omega
    · have he : k=1 := by omega
      subst k
      have h := hp.1
      have hpar := hp.2.2.1
      have hm := hp.2.2.2
      have hpk : P 1=10 := by unfold P; decide
      have hpow : 2^(1+1)%3=1 := by decide
      rw [hpk] at hUeq
      rw [hpow] at hm
      omega
  have hqhi : U/3≤2*P k-2 := by omega
  have hqpar : (U/3)%2=k%2 := by
    have hh := hp.2.2.1
    omega
  obtain ⟨hcan,a,ha⟩ := reduce_ray_spec (show PosQ k (U/3) from ⟨hqlo,hqhi,hqpar⟩)
  change CanonQ k (rayParent k p) at hcan
  change U/3=3^a*(rayParent k p) at ha
  have hwindow : 3^a*rayParent k p≤2*P k-2 ∧ 2*P k-2<3^(a+1)*rayParent k p := by
    rw [ha] at hqhi hmul
    refine ⟨hqhi,?_⟩
    calc
      2*P k-2 < U := by omega
      _ = 3*(3^a*rayParent k p) := hmul.symm
      _ = 3^(a+1)*rayParent k p := by rw [Nat.pow_succ]; ac_rfl
  have hpos : 0<rayParent k p := by have := hcan.1.1; omega
  have hcnt : positiveCount k (rayParent k p)=a := by
    unfold positiveCount
    apply CapMacro.triple_window_unique hpos
    · exact CapMacro.tripleCount_spec hpos hcan.1.2.1
    · exact hwindow
  have hprod : positiveProduct k (rayParent k p)=U := by
    unfold positiveProduct
    rw [hcnt,Nat.pow_succ,show 3^a*3*rayParent k p=3*(3^a*rayParent k p) by ac_rfl,←ha,hmul]
  have hnext := positive_next_equation hpos hcan.1.2.1
  exact ⟨hcan,by omega⟩

theorem ray_parent_inverse {k q : Nat} (hk : 1≤k) (hq : CanonQ k q) :
    rayParent k (positiveNext k q)=q :=
  canonical_positive_next_inj
    (ray_parent_spec hk (positive_next_range hq.1)).1 hq
    (ray_parent_spec hk (positive_next_range hq.1)).2

/-- In ordinary one-band returns, the positive canonical parent is explicit. -/
theorem regular_parent_exact {j q : Nat} (hj : 2≤j)
    (hq : PosQ j q) (hunit : q%3=2^j%3) :
    CanonQ (j-1) (rayParent (j-1) q) ∧
      (signedEvent (j-1) (rayParent (j-1) q)).2=some (j,q) := by
  have hJ : j-1+1=j := by omega
  have hp : ExitP (j-1) q := by
    unfold ExitP
    rw [hJ]
    exact ⟨by have := hq.1; omega,hq.2.1,hq.2.2,hunit⟩
  obtain ⟨hc,he⟩ := ray_parent_spec (by omega : 1≤j-1) hp
  refine ⟨hc,?_⟩
  unfold signedEvent
  rw [if_pos hc.1.2.1]
  dsimp
  rw [he,if_pos (by have := hq.1; omega : j-1+7≤q),hJ]

#print axioms ray_parent_spec
#print axioms ray_parent_inverse
#print axioms regular_parent_exact
end CapSieve
