import Lean
namespace BB6.Agent13P130

private theorem pow16_grow (n : Nat) : n+1 ≤ 2^(16*n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have he : (2:Nat)^(16*(n+1))=65536*2^(16*n) := by
      have hs : 16*(n+1)=16*n+16 := by omega
      rw [hs,Nat.pow_add]
      simp [show (2:Nat)^16=65536 by decide, Nat.mul_comm]
    rw [he]
    omega

theorem pow16_ge_linear (q : Nat) (hq:1≤q) : 65536*q≤2^(16*q) := by
  cases q with
  | zero => omega
  | succ n =>
    have he : (2:Nat)^(16*(n+1))=65536*2^(16*n) := by
      have hs : 16*(n+1)=16*n+16 := by omega
      rw [hs,Nat.pow_add]
      simp [show (2:Nat)^16=65536 by decide, Nat.mul_comm]
    rw [he]
    have h := pow16_grow n
    omega

theorem pow16_dominates_hub (q m side : Nat)
    (hq:29≤q) (hm:m≤10) (hside:side≤9) :
    m+(16*q+side) ≤ 2^(16*q) ∧ 1024 < 2^(16*q) := by
  have hg := pow16_ge_linear q (by omega)
  omega


theorem l0_root_wide (r u : Nat)
  (hu : u+4*(30+256*r)+3=7*2^(16*(30+256*r))) :
  2^10*36 < 4*u+8 := by
  let q := 30+256*r
  have hg := pow16_ge_linear q (by omega)
  have hq : 29≤q := by omega
  dsimp [q] at hg
  omega

theorem l1_root_wide (r u : Nat)
  (hu : u+4*(30+256*r)+3=7*2^(16*(30+256*r))) :
  2^10*36 < 6*u+10 := by
  let q := 30+256*r
  have hg := pow16_ge_linear q (by omega)
  have hq : 29≤q := by omega
  dsimp [q] at hg
  omega

#print axioms pow16_ge_linear
#print axioms l0_root_wide
#print axioms l1_root_wide
#print axioms pow16_dominates_hub
end BB6.Agent13P130
