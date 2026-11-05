import GenericShadow
import P1TwoSector

namespace BB6.Agent8Generic
open BB6.Agent45TwoRoot BB6.Agent4Cone BB6.Agent1

/-- Any two finite shadow certificates meeting the structural hypotheses
    source-certify nonreachability of the original P1 critical reset hub.
    This theorem is uniform in q, rather than an instantiation at one
    congruence class. -/
theorem critical_unreachable_of_shadow
    (q : Nat) (hq : 29 ≤ q)
    (nodes0 nodes1 : List (Nat × Nat))
    (hroot0 : (0,12*q+4) ∈ nodes0)
    (hroot1 : (0,10*q+4) ∈ nodes1)
    (hclosed0 : ∀ m z t v zp, (m,z) ∈ nodes0 →
      z=2^t*v → 2*zp+1=16*q+8+m+t+v → (m+t+1,zp) ∈ nodes0)
    (hclosed1 : ∀ m z t v zp, (m,z) ∈ nodes1 →
      z=2^t*v → 2*zp+1=16*q+9+m+t+v → (m+t+1,zp) ∈ nodes1)
    (hsmall0 : ∀ m z, (m,z)∈nodes0 → m≤10)
    (hsmall1 : ∀ m z, (m,z)∈nodes1 → m≤10)
    (hnodiv0 : ∀ m z, (m,z)∈nodes0 → ¬256∣z)
    (hnodiv1 : ∀ m z, (m,z)∈nodes1 → ¬256∣z) :
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
    g0_blocked q (u2 q) hq hmass hu1 nodes0 hroot0 hclosed0
      hsmall0 hnodiv0 rfl hroot4 hrootodd
  have hblocked1 : Blocked (6*u2 q-2) (2*u2 q+5) :=
    g1_blocked q (u2 q) hq hmass hu1 nodes1 hroot1 hclosed1
      hsmall1 hnodiv1 rfl hroot14 hroot1odd
  intro hr
  have hfeed := (two_sector_critical_iff_feeders q (by omega)).mp hr
  rcases hfeed with h0 | h1
  · exact (blocked_no_reach _ _ hblocked0) h0
  · exact (blocked_no_reach _ _ hblocked1) h1

#print axioms critical_unreachable_of_shadow
end BB6.Agent8Generic
