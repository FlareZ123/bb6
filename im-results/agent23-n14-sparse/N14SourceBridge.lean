import Agent23N14
import ShadowFiniteInvariant

namespace Agent23N14
open BB6.Shadow BB6.Agent1Quarter

private theorem two_pow_ge_succ (k : Nat) : k+1 ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

/-- Authentic critical n=65536*r+14 inverse states admit a finite shadow witness. -/
theorem authentic_n14_sparse_odd_cone_encoded
    (r b d m : Nat) (hr : 1≤r)
    (hcone : OddCone
      (14*2^(65536*r+14)-2*(65536*r+14)-16) 3 b d m)
    (hmod : b%4=0) :
    ∃ w z alpha,
      (m,z) ∈ nodes r ∧ 0<z ∧ 4≤w ∧
      65536*r+19+m=w+z ∧
      2^m*(b+4*w)=alpha*2^(65536*r+12) := by
  let N := 65536*r+12
  let n := 65536*r+14
  let L := 65536*r+19
  let w0 := 32768*r+11
  let z0 := 32768*r+8
  let b0 := 14*2^n-2*n-16
  have hshift : (2:Nat)^n = 4*2^N := by
    have hn : n=N+2 := by omega
    rw [hn, Nat.pow_add]
    simp [Nat.mul_comm]
  have hbound : 4*w0≤56*2^N := by
    have hp := two_pow_ge_succ N
    dsimp [N,w0] at *
    omega
  have henc : b0+4*w0=56*2^N := by
    have hcapacity : 2*n+16≤14*2^n := by
      rw [hshift]
      dsimp [N,n,w0] at *
      omega
    dsimp [b0]
    rw [hshift]
    dsimp [N,n,w0] at *
    omega
  have hmass : b0+3+2*L+3=56*2^N := by
    dsimp [L,w0] at *
    omega
  have hcone0 : OddCone b0 3 b d m := by
    simpa only [b0,n] using hcone
  obtain ⟨w,z,alpha,hmem,hz,hw,hoff,hscaled⟩ :=
    finite_shadow_invariant_lifts_full_cone
      N L b0 3 w0 z0 56 (nodes r)
      hmass (by dsimp [L]; omega) (by dsimp [N]; omega)
      (by dsimp [L,w0,z0]; omega) (by dsimp [w0]; omega)
      (by dsimp [z0]; omega) henc
      (by simpa only [z0] using nodes_root r)
      (fun m z t v zp hm hd hn =>
        nodes_closed r m z t v zp hm hd (by dsimp [L] at hn; omega))
      (fun m z hm => by have h := nodes_small r m z hm; omega)
      (nodes_no256 r)
      b d m hcone0 hmod
  exact ⟨w,z,alpha,hmem,hz,hw,
    by simpa only [L] using hoff,
    by simpa only [N] using hscaled⟩

theorem authentic_n14_sparse_odd_cone_cost
    (r b d m : Nat) (hr : 1≤r)
    (hcone : OddCone
      (14*2^(65536*r+14)-2*(65536*r+14)-16) 3 b d m)
    (hmod : b%4=0) : m≤8 := by
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    authentic_n14_sparse_odd_cone_encoded r b d m hr hcone hmod
  exact nodes_small r m z hmem

#print axioms authentic_n14_sparse_odd_cone_encoded
#print axioms authentic_n14_sparse_odd_cone_cost
end Agent23N14
