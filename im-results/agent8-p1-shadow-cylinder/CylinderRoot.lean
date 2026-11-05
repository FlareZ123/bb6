import CylinderBlocked
import P1TwoSector

namespace BB6.Agent8Cylinder
open BB6.Agent4Cone BB6.Agent45TwoRoot BB6.Agent1Quarter

private theorem q_properties (r : Nat) :
    let q:=29+1024*r
    3≤u2 q ∧ (u2 q)%2=1 ∧
      u2 q+4*q+3=7*2^(16*q) := by
  let q:=29+1024*r
  have hg := pow16_ge_linear q (by omega)
  have he1 : (2:Nat)^1 ∣ 2^(16*q) := Nat.pow_dvd_pow 2 (by omega)
  have he : 2∣(2:Nat)^(16*q) := by simpa using he1
  have hpow : (2:Nat)^(16*q)%2=0 := Nat.dvd_iff_mod_eq_zero.mp he
  dsimp [q,u2] at *
  omega

theorem l0_all_r_blocked (r : Nat) :
    Blocked (4*u2 (29+1024*r)-4) (4*u2 (29+1024*r)+9) := by
  let q:=29+1024*r
  let u:=u2 q
  obtain ⟨hu3,huodd,hu⟩ := q_properties r
  have hcone : OddCone (4*u-4) (4*u+9) (4*u-4) (4*u+9) 0 :=
    OddCone.root
  have huEq : u+4*(29+1024*r)+3=7*2^(16*(29+1024*r)) := by
    simpa [q,u] using hu
  have hu1 : 1≤u := by simpa [u,q] using Nat.le_trans (by omega : 1≤3) hu3
  have hb4 : (4*u-4)%4=0 := by omega
  have hdodd : (4*u+9)%2=1 := by omega
  exact l0_blocked_fuel r u huEq hu1 rfl 11 (4*u-4) (4*u+9) 0
    (by omega) hcone hb4 hdodd

theorem l1_all_r_blocked (r : Nat) :
    Blocked (6*u2 (29+1024*r)-2) (2*u2 (29+1024*r)+5) := by
  let q:=29+1024*r
  let u:=u2 q
  obtain ⟨hu3,huodd,hu⟩ := q_properties r
  have hcone : OddCone (6*u-2) (2*u+5) (6*u-2) (2*u+5) 0 :=
    OddCone.root
  have huEq : u+4*(29+1024*r)+3=7*2^(16*(29+1024*r)) := by
    simpa [q,u] using hu
  have hu1 : 1≤u := by simpa [u,q] using Nat.le_trans (by omega : 1≤3) hu3
  have huOdd : u%2=1 := by simpa [u,q] using huodd
  have hb4 : (6*u-2)%4=0 := by omega
  have hdodd : (2*u+5)%2=1 := by omega
  exact l1_blocked_fuel r u huEq hu1 rfl 11 (6*u-2) (2*u+5) 0
    (by omega) hcone hb4 hdodd

theorem l0_all_r_unreachable (r:Nat) :
    ¬BB6.Agent1.Reach (4*u2 (29+1024*r)-4) (4*u2 (29+1024*r)+9) :=
  blocked_no_reach _ _ (l0_all_r_blocked r)

theorem l1_all_r_unreachable (r:Nat) :
    ¬BB6.Agent1.Reach (6*u2 (29+1024*r)-2) (2*u2 (29+1024*r)+5) :=
  blocked_no_reach _ _ (l1_all_r_blocked r)

#print axioms l0_all_r_blocked
#print axioms l1_all_r_blocked
#print axioms l0_all_r_unreachable
#print axioms l1_all_r_unreachable
end BB6.Agent8Cylinder
