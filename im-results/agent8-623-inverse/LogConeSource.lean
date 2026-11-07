import Agent8DrainFirstSharpSource

/-!
Original source #623 logarithmic two-step safety cones. Every theorem below
concerns successful accelerated transitions on arbitrary synthetic states;
the actual blank-root orbit is not proved to remain in these cones.
-/

namespace BB6.Agent8LogConeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8DrainFirstSharpSource
open BB6.Agent8DrainSevenSource

theorem ternaryOnes_mono (u v : Nat) (h : u≤v) :
    ternaryOnes u ≤ ternaryOnes v := by
  have hu := twice_ones_add_one_eq_pow u
  have hv := twice_ones_add_one_eq_pow v
  have hp := Nat.pow_le_pow_right (by omega : 0<3) h
  omega

theorem next_safe_left_log (a d k : Nat)
    (hgap : d+5+k≤a) (hpower : 2*d+7≤3^k) :
    ∃aa dd, highLevelNext (.D a d) = some (.D aa dd) := by
  have hp := twice_ones_add_one_eq_pow k
  have hbudget : d+3≤ternaryOnes k := by omega
  apply next_safe_right_ones a d
  · intro he
    have h1 : d+5≤a := by omega
    have hk : k≤a-d-5 := by omega
    have hh := ternaryOnes_mono k (a-d-5) hk
    exact ⟨h1,by omega⟩
  · intro he
    have h1 : d+3≤a := by omega
    have hk : k≤a-d-2 := by omega
    have hh := ternaryOnes_mono k (a-d-2) hk
    exact ⟨h1,by omega⟩

theorem drainB_log_two_step (a b d k aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hgap : d+8*b+5+k≤a) (hpower : 2*d+14*b+7≤3^k) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have hf := drainB_first_lower_sharp b a d aa dd hs
  have ht := drainB_third_upper_seven b a d aa dd hs
  have hi : dd+5+k≤aa := by omega
  have hj : 2*dd+7≤3^k := by omega
  exact next_safe_left_log aa dd k hi hj

#print axioms ternaryOnes_mono
#print axioms next_safe_left_log
#print axioms drainB_log_two_step
end BB6.Agent8LogConeSource

namespace BB6.Agent8LogOuterSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8LogConeSource
open BB6.Agent8DrainFirstSharpSource
open BB6.Agent8DrainSevenSource

theorem odd_far_left_log_two_step (a d k aa dd : Nat)
    (ha : 0<a) (hd : d%2=1)
    (hroom : 9*d+39+k ≤ a) (hpow : 14*d+59 ≤ 3^k)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : d%2=1 ∧ a≥d+5 := ⟨hd,by omega⟩
  simp only [highLevelNext, if_neg h0, if_pos h1] at hs
  exact drainB_log_two_step (a-d-5) (d+3) 5 k aa dd hs (by omega) (by omega)

theorem even_far_left_log_two_step (a d k aa dd : Nat)
    (ha : 0<a) (hd : d%2=0)
    (hroom : 9*d+25+k ≤ a) (hpow : 14*d+39 ≤ 3^k)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : d%2=0 ∧ a≥d+3 := ⟨hd,by omega⟩
  simp only [highLevelNext, if_neg h0, if_neg h1, if_pos h2] at hs
  exact drainB_log_two_step (a-d-2) (d+2) 2 k aa dd hs (by omega) (by omega)

theorem odd_far_right_log_two_step (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1)
    (hroom : 9*a+k ≤ d+4) (hpow : 14*a ≤ 3^k)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠1 := by omega
  have h4 : a ≠ d+2 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
    if_neg h3, if_neg h4, if_pos hd] at hs
  exact drainB_log_two_step (d+4-a) (a-1) 3 k aa dd hs (by omega) (by omega)

theorem even_far_right_log_two_step (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0)
    (hroom : 8*a+13+k ≤ d) (hpow : 12*a+23 ≤ 3^k)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠1 := by omega
  have h4 : a ≠ d+2 := by omega
  have h5 : d%2 ≠1 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
    if_neg h3, if_neg h4, if_neg h5] at hs
  cases hev : evalA (d+1-a) a (2*a+5) with
  | none => simp [hev] at hs
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [hev, Option.bind_some] at hs
    have hf := evalA_first_potential (d+1-a) a (2*a+5) a1 b1 d1 hev
    have ht := evalA_third_potential (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hq := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
      (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hbudget1 : d1+8*b1+5+k≤a1 := by omega
    have hbudget2 : 2*d1+14*b1+7≤3^k := by omega
    exact drainB_log_two_step a1 b1 d1 k aa dd hs hbudget1 hbudget2

#print axioms odd_far_left_log_two_step
#print axioms even_far_left_log_two_step
#print axioms odd_far_right_log_two_step
#print axioms even_far_right_log_two_step
end BB6.Agent8LogOuterSource
