import EvenOddLowStopEvenReachIff
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowQuarterTwoForced

private theorem linear_le_power (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- For every low stop index z divisible by four (z=4r), TWO
    successive original-source ancestors are uniquely forced from
    the true blank section orbit. The first is the exact singleton
    incoming edge over R_u; its right-even parent is then an affine
    one-step original-source equivalence. Both steps are genuinely
    iff, at arbitrary time and unbounded z. -/
theorem low_index_multiple_four_reach_iff_two_forced
    (s u : Nat)
    (hs : s%2=0)
    (hu : u+12*s+1=2^(2048*s+129)) :
    BB6.Agent3.CReach (180*u+28) (166*u+25) ↔
    BB6.Agent3.CReach
      ((173*u+24)+((339*u+47)/2)-2)
      ((((339*u+47)/2)-2)/2) := by
  have he : 1024*(2*s)+129=2048*s+129 := by omega
  have hu' : u+6*(2*s)+1=2^(1024*(2*s)+129) := by
    rw [he]
    omega
  have hfirst :=
    BB6.Agent13LowEvenIff.even_low_ray_reach_iff_unique_parent
      (2*s) u hu' (by omega)
  have hp8 : 8 ∣ 2^(2048*s+129) := by
    have hh : (2:Nat)^3∣2^(2048*s+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^3=8 by decide] using hh
  have hpmod : (2^(2048*s+129))%8=0 :=
    Nat.mod_eq_zero_of_dvd hp8
  have humod : u%8=7 := by omega
  have hkm : (339*u+47)%2=0 := by omega
  have hktwice : 2*((339*u+47)/2)=339*u+47 := by
    have hh := Nat.mod_add_div (339*u+47) 2
    omega
  have hke : ((339*u+47)/2)%2=0 := by omega
  have hksum : ((173*u+24)+((339*u+47)/2))%4=1 := by omega
  have hlin : 2048*s+130≤2^(2048*s+129) :=
    linear_le_power _
  have hu6 : 6≤u := by omega
  have hk : 4≤(339*u+47)/2 := by omega
  have hsecond :=
    BB6.Agent15.blank_reach_iff_affine
      (173*u+24) ((339*u+47)/2) hk hke hksum
  exact hfirst.trans hsecond

#print axioms low_index_multiple_four_reach_iff_two_forced
end BB6.Agent13LowQuarterTwoForced
