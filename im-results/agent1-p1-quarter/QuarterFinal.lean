import P1TwoSector
import QuarterCone
namespace BB6.Agent1Quarter
open BB6.Agent4Cone
open BB6.Agent45TwoRoot

/-- Every remaining critical-index family n≡2 or50 (mod64) is unreachable
    from the authentic blank-entry P1 state, uniformly for all q≥1. -/
theorem no_critical_q_mod_four (q : Nat) (hq : 1≤q)
    (hqmod : q%4=0 ∨ q%4=3) :
    ¬ BB6.Agent1.Reach 2
       (14*2^(16*q+2)-2*(16*q+2)-10) := by
  intro hr
  have hfeed := (two_sector_critical_iff_feeders q hq).mp hr
  let u := u2 q
  have hdom : 64*(q+1) ≤ 2^(16*q) := pow16_dom q hq
  have hform : u+4*q+3=7*2^(16*q) := by
    dsimp [u,u2]
    omega
  have hlow : 61≤u := by omega
  have hpmod : (2^(16*q))%32=0 := by
    have he : 2^5 ∣ 2^(16*q) := Nat.pow_dvd_pow 2 (by omega)
    have hd : 32 ∣ 2^(16*q) := by
      simpa [show (2:Nat)^5=32 by decide] using he
    exact Nat.dvd_iff_mod_eq_zero.mp hd
  have hcases : q%8=0 ∨ q%8=3 ∨ q%8=4 ∨ q%8=7 := by omega
  rcases hcases with h0 | h3 | h4 | h7
  · have hmod : u%32=29 := by omega
    let w := u/32
    have hu : u=32*w+29 := by dsimp [w]; omega
    have hw : 1≤w := by omega
    rcases hfeed with hL0 | hL1
    · have hblocked := cone_29_l0_final q u w hq hw hu hform
      have hleft : 4*u-4=128*w+112 := by omega
      have hright : 4*u+9=128*w+125 := by omega
      rw [hleft,hright] at hL0
      exact (blocked_no_reach _ _ hblocked) hL0
    · have hblocked := cone_29_l1_final q u w hq hw hu hform
      have hleft : 6*u-2=192*w+172 := by omega
      have hright : 2*u+5=64*w+63 := by omega
      rw [hleft,hright] at hL1
      exact (blocked_no_reach _ _ hblocked) hL1
  · have hmod : u%32=17 := by omega
    let w := u/32
    have hu : u=32*w+17 := by dsimp [w]; omega
    have hw : 1≤w := by omega
    rcases hfeed with hL0 | hL1
    · have hblocked := cone_17_l0_final q u w hq hw hu hform
      have hleft : 4*u-4=128*w+64 := by omega
      have hright : 4*u+9=128*w+77 := by omega
      rw [hleft,hright] at hL0
      exact (blocked_no_reach _ _ hblocked) hL0
    · have hblocked := cone_17_l1_final q u w hq hw hu hform
      have hleft : 6*u-2=192*w+100 := by omega
      have hright : 2*u+5=64*w+39 := by omega
      rw [hleft,hright] at hL1
      exact (blocked_no_reach _ _ hblocked) hL1
  · have hmod : u%32=13 := by omega
    let w := u/32
    have hu : u=32*w+13 := by dsimp [w]; omega
    have hw : 1≤w := by omega
    rcases hfeed with hL0 | hL1
    · have hblocked := cone_13_l0_final q u w hq hw hu hform
      have hleft : 4*u-4=128*w+48 := by omega
      have hright : 4*u+9=128*w+61 := by omega
      rw [hleft,hright] at hL0
      exact (blocked_no_reach _ _ hblocked) hL0
    · have hblocked := cone_13_l1_final q u w hq hw hu hform
      have hleft : 6*u-2=192*w+76 := by omega
      have hright : 2*u+5=64*w+31 := by omega
      rw [hleft,hright] at hL1
      exact (blocked_no_reach _ _ hblocked) hL1
  · have hmod : u%32=1 := by omega
    let w := u/32
    have hu : u=32*w+1 := by dsimp [w]; omega
    have hw : 1≤w := by omega
    rcases hfeed with hL0 | hL1
    · have hblocked := cone_1_l0_final q u w hq hw hu hform
      have hleft : 4*u-4=128*w+0 := by omega
      have hright : 4*u+9=128*w+13 := by omega
      rw [hleft,hright] at hL0
      exact (blocked_no_reach _ _ hblocked) hL0
    · have hblocked := cone_1_l1_final q u w hq hw hu hform
      have hleft : 6*u-2=192*w+4 := by omega
      have hright : 2*u+5=64*w+7 := by omega
      rw [hleft,hright] at hL1
      exact (blocked_no_reach _ _ hblocked) hL1

#print axioms no_critical_q_mod_four
end BB6.Agent1Quarter
