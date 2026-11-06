import ShadowFiniteBudgetK

namespace Agent23N14K9
open BB6.Shadow BB6.Agent1Quarter BB6.Agent9Budget

private theorem two_pow_ge_succ (k : Nat) : k+1 ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

/-- Uniform genuine-source inverse certificate for critical n=16q+14. -/
theorem cone_encoded
    (q : Nat) (hq : 1≤q)
    (nodes : List (Nat × Nat))
    (hroot : (0,8*q+8)∈nodes)
    (hclosed : ∀ m z t v zp, (m,z)∈nodes →
      z=2^t*v → 2*zp+1=16*q+19+m+t+v →
      (m+t+1,zp)∈nodes)
    (hsmall : ∀ m z, (m,z)∈nodes → m≤8)
    (hnodiv : ∀ m z, (m,z)∈nodes → ¬512∣z)
    (b d m : Nat)
    (hcone : OddCone
      (14*2^(16*q+14)-2*(16*q+14)-16) 3 b d m)
    (hmod : b%4=0) :
    ∃ w z alpha,
      (m,z)∈nodes ∧ 0<z ∧ 4≤w ∧
      16*q+19+m=w+z ∧
      2^m*(b+4*w)=alpha*2^(16*q+12) := by
  let N := 16*q+12
  let n := 16*q+14
  let L := 16*q+19
  let w0 := 8*q+11
  let z0 := 8*q+8
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
    finite_shadow_invariant_lifts_full_cone_K_budget
      9 8 N L b0 3 w0 z0 56 nodes
      hmass (by dsimp [L]; omega) (by dsimp [N]; omega)
      (by dsimp [L,w0,z0]; omega) (by dsimp [w0]; omega)
      (by dsimp [z0]; omega) henc
      (by simpa only [z0] using hroot)
      (fun m z t v zp hm hd hn =>
        hclosed m z t v zp hm hd (by dsimp [L] at hn; omega))
      (fun m z hm => by have h := hsmall m z hm; omega)
      hnodiv
      b d m hcone0 hmod
  exact ⟨w,z,alpha,hmem,hz,hw,
    by simpa only [L] using hoff,
    by simpa only [N] using hscaled⟩

#print axioms cone_encoded
end Agent23N14K9
