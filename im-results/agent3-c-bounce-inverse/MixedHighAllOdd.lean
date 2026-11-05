import MixedFourNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem exp_dominates_linear (n : Nat) :
    n+11 ≤ 2^(2*n+4) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1)+4=(2*n+4)+2 := by omega
      rw [he,Nat.pow_add]
      have h4 : (2:Nat)^2=4 := by decide
      rw [h4]
      omega

/-- Original-source arithmetic obstruction for an entire high stopping
    parameter sector, involving every m≥5 with m≡1 mod4 and j+m≡2 mod32.
    No finite simulation bound appears in the proof. -/
theorem mixed_high_all_m_one_mod4_unreachable
    (j m k : Nat) (hm : 5≤m) (hm4 : m%4=1)
    (hj : (j+m)%32=2)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ CReach (2*j+3) k := by
  have hb : m+10≤2^(2*m+2) := by
    cases m with
    | zero => omega
    | succ n =>
        simpa only [show 2*(n+1)+2=2*n+4 by omega]
          using exp_dominates_linear n
  have hmulp : j≤2^(2*m+2)*j := by
    have hle : 1≤2^(2*m+2) := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hle
  have hmuladd : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  have hsmall : 24≤(2*j+3)+k ∧ 5≤k := by
    omega
  have hpow : 256 ∣ 2^(2*m+2) := by
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdiv : 256 ∣ k+j+3*m+5 := by
    rw [hstop]
    obtain ⟨v,hv⟩ := hpow
    refine ⟨v*(j+3),?_⟩
    rw [hv]
    ac_rfl
  obtain ⟨t,ht⟩ := hdiv
  let a1 := ((2*j+3)+k-4)/2
  let k1 := ((2*j+3)+3*k-10)/4
  let a2 := a1+k1-2
  let k2 := (k1-2)/2
  have hfirst : oddLowGate (2*j+3) k := by
    simp only [oddLowGate]
    omega
  rcases hfirst with ⟨hx,hy,hy5,h4,h16,hsize⟩
  intro hr
  have h1 : CReach a1 k1 := by
    simpa only [CReach] using
      (oddodd_lowval_blank_reach_iff (2*j+3) k hx hy hy5 h4 h16 hsize).mp hr
  have hsecond : BB6.Agent46.sixEvenRightGate a1 k1 := by
    simp only [BB6.Agent46.sixEvenRightGate]
    dsimp [a1,k1]
    omega
  rcases hsecond with ⟨h6,he,h0,h7⟩
  have h2 : CReach a2 k2 :=
    (six_even_right_blank_reach_iff a1 k1 h6 he h0 h7).mp h1
  have hbad : 5≤k2 ∧ k2%2=1 ∧ (a2+k2)%4=1 := by
    dsimp [a1,k1,a2,k2]
    omega
  rcases h2 with ⟨time,hn⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
  | succ n =>
      have hi := blank_section_odd_image n a2 k2 hn hbad.1 hbad.2.1
      omega

#print axioms mixed_high_all_m_one_mod4_unreachable
end BB6.Agent3
