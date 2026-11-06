import OddOddLowVal
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent23C26
open BB6.Agent3 BB6.Agent46

/-- Five exact source inverse steps forbid the full low-target cylinder. -/
theorem blank_no_one_mod256_26 (t : Nat) (ht : 1 ≤ t) :
    ¬ BB6.Agent3.CReach 1 (256*t+26) := by
  intro h
  have h1 : BB6.Agent3.CReach (256*t+25) (128*t+12) := by
    have hh := (six_even_right_blank_reach_iff 1 (256*t+26)
      (by omega) (by omega) (by omega) (by omega)).mp h
    have hx : 1+(256*t+26)-2=256*t+25 := by omega
    have hy : ((256*t+26)-2)/2=128*t+12 := by omega
    simpa only [hx,hy] using hh
  have h2 : BB6.Agent3.CReach (384*t+35) (64*t+5) := by
    have hh := (six_even_right_blank_reach_iff (256*t+25) (128*t+12)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have hx : (256*t+25)+(128*t+12)-2=384*t+35 := by omega
    have hy : ((128*t+12)-2)/2=64*t+5 := by omega
    simpa only [hx,hy] using hh
  have h3 : BB6.Agent3.CReach (224*t+18) (144*t+10) := by
    have hh := (oddodd_lowval_blank_reach_iff (384*t+35) (64*t+5)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h2
    have hx : ((384*t+35)+(64*t+5)-4)/2=224*t+18 := by omega
    have hy : ((384*t+35)+3*(64*t+5)-10)/4=144*t+10 := by omega
    simpa only [hx,hy, BB6.Agent3.CReach] using hh
  have h4 : BB6.Agent3.CReach (368*t+26) (72*t+4) := by
    have hh := (six_even_right_blank_reach_iff (224*t+18) (144*t+10)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have hx : (224*t+18)+(144*t+10)-2=368*t+26 := by omega
    have hy : ((144*t+10)-2)/2=72*t+4 := by omega
    simpa only [hx,hy] using hh
  have h5 : BB6.Agent3.CReach (440*t+28) (36*t+1) := by
    have hh := (six_even_right_blank_reach_iff (368*t+26) (72*t+4)
      (by omega) (by omega) (by omega) (by omega)).mp h4
    have hx : (368*t+26)+(72*t+4)-2=440*t+28 := by omega
    have hy : ((72*t+4)-2)/2=36*t+1 := by omega
    simpa only [hx,hy] using hh
  rcases h5 with ⟨n,hn⟩
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n (440*t+28) (36*t+1)
        hn (by omega) (by omega)
      omega

private theorem low_margin (n : Nat) :
    3*(n+3)+286 ≤ 2^(2*(n+3)+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1+3)+3=(2*(n+3)+3)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- The original low stopping family m=246 (mod 256) lies inside
    the disjoint source cylinder. -/
theorem blank_no_low_m_246_mod256 (m k : Nat)
    (hm : m%256=246) (hgate : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hm3 : 3≤m := by omega
  have hpow256 : 256 ∣ 2^(2*m+3) := by
    change 2^8 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hzero : (k+3*m+4)%256=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hpow256
  have hkmod : k%256=26 := by omega
  obtain ⟨n,hn⟩ : ∃ n, m=n+3 := ⟨m-3,by omega⟩
  have hb := low_margin n
  have hklarge : 282≤k := by
    rw [hn] at hgate
    omega
  have ht : 1≤k/256 := by omega
  have hkform : k=256*(k/256)+26 := by omega
  rw [hkform]
  exact blank_no_one_mod256_26 (k/256) ht

#print axioms blank_no_low_m_246_mod256
#print axioms blank_no_one_mod256_26
end BB6.Agent23C26
