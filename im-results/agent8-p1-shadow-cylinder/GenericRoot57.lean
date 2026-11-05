import GenericShadow
import CylinderArithmetic57

namespace BB6.Agent8Generic
open BB6.Agent8Cylinder BB6.Agent45TwoRoot BB6.Agent4Cone

private theorem q_properties (q : Nat) (hq:29≤q) :
    3≤u2 q ∧ (u2 q)%2=1 ∧
      u2 q+4*q+3=7*2^(16*q) := by
  have hg := pow16_ge_linear q (by omega)
  have he1 : (2:Nat)^1 ∣ 2^(16*q) := Nat.pow_dvd_pow 2 (by omega)
  have he : 2∣(2:Nat)^(16*q) := by simpa using he1
  have hpow : (2:Nat)^(16*q)%2=0 := Nat.dvd_iff_mod_eq_zero.mp he
  dsimp [u2]
  omega

theorem q57_l0_blocked (r:Nat) :
    Blocked (4*u2 (57+1024*r)-4) (4*u2 (57+1024*r)+9) := by
  let q:=57+1024*r
  let u:=u2 q
  have hq:29≤q := by omega
  obtain ⟨hu3,huodd,hu⟩ := q_properties q hq
  have hroot : (0,12*q+4)∈l0_57Nodes r := by
    simp [l0_57Nodes,q]
    omega
  have hu1 : 1≤u := by simpa [u] using Nat.le_trans (by omega : 1≤3) hu3
  have hb4 : (4*u-4)%4=0 := by omega
  have hdodd : (4*u+9)%2=1 := by omega
  exact g0_blocked q u hq hu hu1 (l0_57Nodes r) hroot
    (fun m z t v zp hm hd hn => l0_57_closed r m z t v zp hm hd (by simpa [q] using hn))
    (fun m z hm => l0_57_small r m z hm)
    (fun m z hm => l0_57_no256 r m z hm)
    rfl hb4 hdodd

theorem q57_l1_blocked (r:Nat) :
    Blocked (6*u2 (57+1024*r)-2) (2*u2 (57+1024*r)+5) := by
  let q:=57+1024*r
  let u:=u2 q
  have hq:29≤q := by omega
  obtain ⟨hu3,huodd,hu⟩ := q_properties q hq
  have hroot : (0,10*q+4)∈l1_57Nodes r := by
    simp [l1_57Nodes,q]
    omega
  have hu1 : 1≤u := by simpa [u] using Nat.le_trans (by omega : 1≤3) hu3
  have hb4 : (6*u-2)%4=0 := by omega
  have hdodd : (2*u+5)%2=1 := by omega
  exact g1_blocked q u hq hu hu1 (l1_57Nodes r) hroot
    (fun m z t v zp hm hd hn => l1_57_closed r m z t v zp hm hd (by simpa [q] using hn))
    (fun m z hm => l1_57_small r m z hm)
    (fun m z hm => l1_57_no256 r m z hm)
    rfl hb4 hdodd

theorem critical_914_mod16384_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(914+16384*r)-2*(914+16384*r)-10) := by
  let q := 57+1024*r
  have he : 16*q+2=914+16384*r := by dsimp [q]; omega
  intro hreach
  have hr : BB6.Agent1.Reach 2
      (14*2^(16*q+2)-2*(16*q+2)-10) := by
    simpa only [he] using hreach
  have htwo := (two_sector_critical_iff_feeders q (by omega)).mp hr
  rcases htwo with h0 | h1
  · exact (blocked_no_reach _ _ (q57_l0_blocked r)) (by simpa only [q] using h0)
  · exact (blocked_no_reach _ _ (q57_l1_blocked r)) (by simpa only [q] using h1)

#print axioms critical_914_mod16384_unreachable
end BB6.Agent8Generic
