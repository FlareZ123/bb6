import DyadicSixCone
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace BB6.Agent19ThreeCone
open BB6.Agent46 BB6.Agent3

/-- Complementary all-depth inverse cone. For odd base u=3 modulo4,
    the forbidden mass class is 3 modulo8. This is disjoint from
    Agent19's original u=1, mass=0 dyadic six-cone, and holds for
    every arbitrary natural depth r in the genuine blank section. -/
theorem dyadic_three_cone_no_blank (r a b u : Nat)
    (hu : 9≤u) (hu4 : u%4=3)
    (hb : b+2=2^r*u)
    (hmass : (a+2*b+4*r)%8=3) :
    ¬ BB6.Agent3.CReach a b := by
  induction r generalizing a b with
  | zero =>
      intro hr
      have hmod : (a+b)%4=2 := by omega
      have hbig : 5≤b := by omega
      have hodd : b%2=1 := by omega
      rcases hr with ⟨time,htrace⟩
      cases time with
      | zero =>
          simp [BB6.Agent8Section.run] at htrace <;> omega
      | succ t =>
          have h := BB6.Agent3.blank_section_odd_image
            t a b htrace hbig hodd
          omega
  | succ s ih =>
      intro hr
      have hpower : (2:Nat)^(s+1)*u=2*(2^s*u) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hEven : b%2=0 := by omega
      have hB : 6≤b := by
        have hp : 1≤(2:Nat)^s := Nat.pow_pos (by decide)
        have hmul : u≤(2:Nat)^s*u := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right u hp
        omega
      have hmod : (a+b)%8≠0 ∧ (a+b)%8≠7 := by
        by_cases hs : s=0
        · subst s
          have hb8 : b%8=4 := by
            have hb2 : b+2=2*u := by simpa using hb
            omega
          have hr8 : (a+2*b+4)%8=3 := by simpa using hmass
          omega
        · have hp : (2:Nat)^2 ∣ 2^(s+1) :=
            Nat.pow_dvd_pow 2 (by omega)
          have hpd : 4 ∣ 2^(s+1) := by simpa using hp
          rcases hpd with ⟨v,hv⟩
          have hd : 4∣b+2 := by
            refine ⟨v*u, ?_⟩
            rw [hb,hv]
            simp only [Nat.mul_assoc]
          have hb4 : b%4=2 := by omega
          omega
      have hnext : BB6.Agent3.CReach (a+b-2) ((b-2)/2) :=
        (BB6.Agent46.six_even_right_blank_reach_iff a b
          hB hEven hmod.1 hmod.2).mp hr
      have hbnext : ((b-2)/2)+2=2^s*u := by omega
      have hmassnext :
          ((a+b-2)+2*((b-2)/2)+4*s)%8=3 := by omega
      exact ih (a+b-2) ((b-2)/2) hbnext hmassnext hnext

#print axioms dyadic_three_cone_no_blank
end BB6.Agent19ThreeCone
