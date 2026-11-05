import MixedFourNormalize
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

theorem low_four_pow_extra (n : Nat) :
    3*(n+1)+24≤2^(2*(n+1)+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have h : 2*(n+1+1)+3=(2*(n+1)+3)+2 := by omega
      rw [h,Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

/-- A whole previously omitted low Machine C stopping-family modulus:
    every exponent m≡4 mod8 is an authentic stopping input,
    permanently excluded from the true blank section orbit.
    The sole immediate ancestor is in the global forbidden odd image. -/
theorem mixed_low_m_four_mod8_stops_unreachable (m k : Nat)
    (hm : m%8=4)
    (hstop : k+3*m+4=2^(2*m+3)) :
    secNext (1,k)=none ∧ ¬ CReach 1 k := by
  have hpow : 8 ∣ 2^(2*m+3) := by
    change 2^3 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod : (k+3*m+4)%8=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk8 : k%8=0 := by omega
  have hbig : 3*m+24≤2^(2*m+3) := by
    obtain ⟨q,hq⟩ : ∃ q : Nat, m=q+1 := ⟨m-1,by omega⟩
    subst m
    exact low_four_pow_extra q
  have hk20 : 20≤k := by omega
  have hk4 : 4≤k := by omega
  constructor
  · apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right
    left
    exact ⟨rfl,m,hstop⟩
  · intro hr
    have hparent : CReach (k-1) ((k-2)/2) := by
      have hp := (BB6.Agent15.blank_reach_iff_affine 1 k hk4
        (by omega) (by omega)).mp hr
      have hx : 1+k-2=k-1 := by omega
      simpa only [hx] using hp
    have hbad : 5≤(k-2)/2 ∧ ((k-2)/2)%2=1 ∧
        ((k-1)+(k-2)/2)%4=2 := by
      omega
    rcases hparent with ⟨time,hn⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hn
        omega
    | succ t =>
        have hi := blank_section_odd_image t (k-1) ((k-2)/2)
          hn hbad.1 hbad.2.1
        omega

#print axioms mixed_low_m_four_mod8_stops_unreachable
end BB6.Agent3
