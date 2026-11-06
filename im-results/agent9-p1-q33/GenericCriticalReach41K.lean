import GenericShadowReach41K
import P1TwoSector

namespace BB6.Agent9Generic41Reach
open BB6.Agent45TwoRoot BB6.Agent4Cone BB6.Agent1 BB6.Precision

/-- Any two source-authentic shadow-path boundedness certificates
    source-certify nonreachability of the original P1 critical reset hub.
    This theorem is uniform in q, rather than an instantiation at one
    congruence class. -/
theorem critical_unreachable_of_reach41K
    (q : Nat) (hq : 29 ≤ q)
    (hsmall0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → m≤41)
    (hsmall1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → m≤41)
    (hnodiv0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → ¬1024∣z)
    (hnodiv1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → ¬1024∣z) :
    ¬ Reach 2 (14*2^(16*q+2)-2*(16*q+2)-10) := by
  have hpow := BB6.Agent8Cylinder.pow16_ge_linear q (by omega)
  have h16 : 1≤16*q := by omega
  have htwo : 2∣(2:Nat)^(16*q) := by
    have h := Nat.pow_dvd_pow 2 h16
    simpa using h
  have hparity : (2:Nat)^(16*q)%2=0 :=
    Nat.dvd_iff_mod_eq_zero.mp htwo
  have hmass : u2 q+4*q+3=7*2^(16*q) := by
    dsimp [u2]
    omega
  have hu1 : 1≤u2 q := by
    dsimp [u2]
    omega
  have hodd : u2 q%2=1 := by
    dsimp [u2]
    omega
  have hroot4 : (4*u2 q-4)%4=0 := by omega
  have hrootodd : (4*u2 q+9)%2=1 := by omega
  have hroot14 : (6*u2 q-2)%4=0 := by omega
  have hroot1odd : (2*u2 q+5)%2=1 := by omega
  have hblocked0 : Blocked (4*u2 q-4) (4*u2 q+9) :=
    g0_blocked q (u2 q) hq hmass hu1 hsmall0 hnodiv0 rfl hroot4 hrootodd
  have hblocked1 : Blocked (6*u2 q-2) (2*u2 q+5) :=
    g1_blocked q (u2 q) hq hmass hu1 hsmall1 hnodiv1 rfl hroot14 hroot1odd
  intro hr
  have hfeed := (two_sector_critical_iff_feeders q (by omega)).mp hr
  rcases hfeed with h0 | h1
  · exact (blocked_no_reach _ _ hblocked0) h0
  · exact (blocked_no_reach _ _ hblocked1) h1

#print axioms critical_unreachable_of_reach41K
end BB6.Agent9Generic41Reach
