import SheepEvenInverseAlgebra
set_option maxHeartbeats 2000000

namespace Sheep138ExactParents

private def R (k : Nat) : Nat := 2^(138+4860*k)

private theorem r_big (k : Nat) : 1024 ≤ R k := by
  have hp : 2^10 ≤ 2^(138+4860*k) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  simpa [R] using hp

private theorem r_even (k : Nat) : R k%2=0 := by
  unfold R
  rw [show 138+4860*k=(137+4860*k)+1 by omega,Nat.pow_succ]
  omega

private theorem r_mod15 (k : Nat) : R k%15=4 := by
  have hp : 2^4%15=1 := by decide
  have he : 138+4860*k=2+4*(34+1215*k) := by omega
  have hp2 : (2^4)^(34+1215*k)%15=1 := by
    rw [Nat.pow_mod (2^4) (34+1215*k) 15, hp]
    simp
  unfold R
  rw [he,Nat.pow_add,Nat.pow_mul,Nat.mul_mod,hp2]

private theorem r_mod81 (k : Nat) : R k%81=73 := by
  have hp : 2^54%81=1 := by decide
  have he : 138+4860*k=30+54*(2+90*k) := by omega
  have hp2 : (2^54)^(2+90*k)%81=1 := by
    rw [Nat.pow_mod (2^54) (2+90*k) 81, hp]
    simp
  unfold R
  rw [he,Nat.pow_add,Nat.pow_mul,Nat.mul_mod,hp2]

private def v1 (k : Nat) : Nat := (4*R k-1)/15
private def u1 (k : Nat) : Nat := (R k-1)/3
private def v2 (k : Nat) : Nat := (8*R k-17)/81
private def u2 (k : Nat) : Nat := (R k-1)/9

private theorem balances (k : Nat) :
    15*v1 k+1=4*R k ∧ 3*u1 k+1=R k ∧
    81*v2 k+17=8*R k ∧ 9*u2 k+1=R k := by
  have h15 := r_mod15 k
  have h81 := r_mod81 k
  have hb := r_big k
  have hmod9 : R k %9 =1 := by omega
  constructor
  · dsimp [v1]
    omega
  constructor
  · dsimp [u1]
    omega
  constructor
  · dsimp [v2]
    omega
  · dsimp [u2]
    omega

private theorem valid1 (k : Nat) :
    5≤v1 k ∧ v1 k%2=1 ∧ u1 k%2=1 ∧
    2*(1+2*u1 k)+1=5*v1 k+2 := by
  have ⟨h1,h2,_,_⟩ := balances k
  have hb := r_big k
  have he := r_even k
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

private theorem valid2 (k : Nat) :
    5≤v2 k ∧ v2 k%2=1 ∧ u2 k%2=1 ∧
    2*(1+4*u2 k)+1=9*v2 k+4 := by
  have ⟨_,_,h3,h4⟩ := balances k
  have hb := r_big k
  have he := r_even k
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-- A uniformly constructive pair of genuine, distinct generic inverse
branches to every power in the r138 family, using the exact generic Sheep
E-equation. The seed's reachability is NOT claimed. -/
theorem two_generic_parents (k : Nat) :
    ∃ x1 x2 : Nat,
      x1 ≠ x2 ∧
      SheepEvenInverseAlgebra.GenericEdge x1 (R k) ∧
      SheepEvenInverseAlgebra.GenericEdge x2 (R k) ∧
      15*x1+2=2^(141+4860*k) ∧
      81*x2+68=2^(143+4860*k) := by
  let x1 := 2*v1 k
  let x2 := 4*v2 k
  have ⟨h1,h2,h3,h4⟩ := balances k
  have ⟨hv1,ho1,hu1,hz1⟩ := valid1 k
  have ⟨hv2,ho2,hu2,hz2⟩ := valid2 k
  have hp1 : 2^(141+4860*k)=8*R k := by
    dsimp [R]
    rw [show 141+4860*k=(138+4860*k)+3 by omega,Nat.pow_add]
    omega
  have hp2 : 2^(143+4860*k)=32*R k := by
    dsimp [R]
    rw [show 143+4860*k=(138+4860*k)+5 by omega,Nat.pow_add]
    omega
  have hb := r_big k
  have hleft : 15*x1+2=2^(141+4860*k) := by
    dsimp [x1]
    rw [hp1]
    omega
  have hright : 81*x2+68=2^(143+4860*k) := by
    dsimp [x2]
    rw [hp2]
    omega
  refine ⟨x1,x2,?_,?_,?_,hleft,hright⟩
  · intro heq
    have hxl : x1=x2 := heq
    omega
  · exact ⟨1,1,v1 k,u1 k,by omega,hv1,ho1,hu1,rfl,
      by simpa using hz1,by omega⟩
  · exact ⟨2,2,v2 k,u2 k,by omega,hv2,ho2,hu2,rfl,
      by simpa using hz2,by omega⟩

#print axioms two_generic_parents
end Sheep138ExactParents
