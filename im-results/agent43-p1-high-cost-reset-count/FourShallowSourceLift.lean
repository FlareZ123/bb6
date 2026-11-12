import SourceLowDepth
import FourShallowSourceModel
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FourShallowSourceLift

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent43SourceWord
open BB6.Agent43FourShallowSourceModel BB6.Agent43TwoRun

private theorem source_two_chain_mass (n s b d m B D M : Nat)
    (h : SourceTwoChain n s b d m B D M)
    (hmass : b+d+2*m+2*n+13=14*2^n) :
    B+D+2*M+2*n+13=14*2^n := by
  induction h with
  | empty => exact hmass
  | append s b d m B D M k c prev hb hb4 hd hi hk hc ih =>
      have hprev := ih hmass
      have hInv := (inverseAt_iff_power_mass B D 2 k c (by omega) hb4 hd).mp hi
      have hMass : 2*k+c+2*2+2=B+D := by omega
      omega

/-- Four genuine depth-0/1 inverseAt transitions, with arbitrary depth-two
runs between them, cannot reach the exact shifted wall for n>=76. -/
theorem source_low_word_four_no_wall
    (n b d m : Nat) (hn : 76≤n)
    (h : SourceLowWord n 4 (14*2^n-2*n-16) 3 0 b d m)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  cases h with
  | shallow _ _ _ _ B6 D6 M6 t4 k4 c4 r _ _ _ prev4 hb4 hb44 hd4 hi4 hk4 hc4 ht4 tail4 =>
    cases prev4 with
    | shallow _ _ _ _ B4 D4 M4 t3 k3 c3 w _ _ _ prev3 hb3 hb34 hd3 hi3 hk3 hc3 ht3 mid3 =>
      cases prev3 with
      | shallow _ _ _ _ B2 D2 M2 t2 k2 c2 v _ _ _ prev2 hb2 hb24 hd2 hi2 hk2 hc2 ht2 mid2 =>
        cases prev2 with
        | shallow _ _ _ _ B0 D0 M0 t1 k1 c1 u _ _ _ prev1 hb1 hb14 hd1 hi1 hk1 hc1 ht1 mid1 =>
          cases prev1 with
          | two s _ _ _ _ _ _ pre =>
            have hrootMass :
                (14*2^n-2*n-16)+3+2*0+2*n+13=14*2^n := by omega
            have hmass0 := source_two_chain_mass n s
              (14*2^n-2*n-16) 3 0 B0 D0 M0 pre hrootMass
            have hInv1 := (inverseAt_iff_power_mass B0 D0 t1 k1 c1
              (by omega) hb14 hd1).mp hi1
            have hMassStep1 : 2*k1+c1+2*t1+2=B0+D0 := by omega
            have hmass1 :
                (2*k1-4)+(c1+4)+2*(M0+t1+1)+2*n+13=14*2^n := by omega
            have hmass2 := source_two_chain_mass n u
              (2*k1-4) (c1+4) (M0+t1+1) B2 D2 M2 mid1 hmass1
            have hInv2 := (inverseAt_iff_power_mass B2 D2 t2 k2 c2
              (by omega) hb24 hd2).mp hi2
            have hMassStep2 : 2*k2+c2+2*t2+2=B2+D2 := by omega
            have hmass3 :
                (2*k2-4)+(c2+4)+2*(M2+t2+1)+2*n+13=14*2^n := by omega
            have hmass4 := source_two_chain_mass n v
              (2*k2-4) (c2+4) (M2+t2+1) B4 D4 M4 mid2 hmass3
            have hInv3 := (inverseAt_iff_power_mass B4 D4 t3 k3 c3
              (by omega) hb34 hd3).mp hi3
            have hMassStep3 : 2*k3+c3+2*t3+2=B4+D4 := by omega
            have hmass5 :
                (2*k3-4)+(c3+4)+2*(M4+t3+1)+2*n+13=14*2^n := by omega
            have hmass6 := source_two_chain_mass n w
              (2*k3-4) (c3+4) (M4+t3+1) B6 D6 M6 mid3 hmass5
            have hInv4 := (inverseAt_iff_power_mass B6 D6 t4 k4 c4
              (by omega) hb44 hd4).mp hi4
            have hMassStep4 : 2*k4+c4+2*t4+2=B6+D6 := by omega
            have hmass7 :
                (2*k4-4)+(c4+4)+2*(M6+t4+1)+2*n+13=14*2^n := by omega

            obtain ⟨alpha,C1,L1,O1,hA11,hA12,hC1,hL1,hL1max,hO1,hAlpha1,hpr1,hSh1⟩ :=
              source_shallow_profile n B0 D0 M0 t1 k1 c1 hmass0
                hb1 hb14 hd1 hi1 hk1 hc1 ht1
            obtain ⟨beta,C2,L2,O2,hA21,hA22,hC2,hL2,hL2max,hO2,hAlpha2,hpr2,hSh2⟩ :=
              source_shallow_profile n B2 D2 M2 t2 k2 c2 hmass2
                hb2 hb24 hd2 hi2 hk2 hc2 ht2
            obtain ⟨gamma,C3,L3,O3,hA31,hA32,hC3,hL3,hL3max,hO3,hAlpha3,hpr3,hSh3⟩ :=
              source_shallow_profile n B4 D4 M4 t3 k3 c3 hmass4
                hb3 hb34 hd3 hi3 hk3 hc3 ht3
            obtain ⟨delta,C4,L4,O4,hA41,hA42,hC4,hL4,hL4max,hO4,hAlpha4,hpr4,hSh4⟩ :=
              source_shallow_profile n B6 D6 M6 t4 k4 c4 hmass6
                hb4 hb44 hd4 hi4 hk4 hc4 ht4

            let Wa : Int := (B0:Int)+4*(M0:Int)+4*(n:Int)+20
            let Ba : Int := (M0:Int)+(n:Int)+6
            let Wb : Int := ((2*k1-4:Nat):Int)+4*((M0+t1+1:Nat):Int)+4*(n:Int)+20
            let Wc : Int := (B2:Int)+4*(M2:Int)+4*(n:Int)+20
            let Bc : Int := (M2:Int)+(n:Int)+6
            let Wd : Int := ((2*k2-4:Nat):Int)+4*((M2+t2+1:Nat):Int)+4*(n:Int)+20
            let We : Int := (B4:Int)+4*(M4:Int)+4*(n:Int)+20
            let Be : Int := (M4:Int)+(n:Int)+6
            let Wf : Int := ((2*k3-4:Nat):Int)+4*((M4+t3+1:Nat):Int)+4*(n:Int)+20
            let Wg : Int := (B6:Int)+4*(M6:Int)+4*(n:Int)+20
            let Bg : Int := (M6:Int)+(n:Int)+6
            let Wh : Int := ((2*k4-4:Nat):Int)+4*((M6+t4+1:Nat):Int)+4*(n:Int)+20
            let Wj : Int := (b:Int)+4*(m:Int)+4*(n:Int)+20
            let Bj : Int := (m:Int)+(n:Int)+6

            have hB1 : Ba+(alpha:Int)=(M0+t1+1:Int)+(n:Int)+6 := by
              dsimp [Ba]
              omega
            have hB2 : Bc+(beta:Int)=(M2+t2+1:Int)+(n:Int)+6 := by
              dsimp [Bc]
              omega
            have hB3 : Be+(gamma:Int)=(M4+t3+1:Int)+(n:Int)+6 := by
              dsimp [Be]
              omega
            have hB4 : Bg+(delta:Int)=(M6+t4+1:Int)+(n:Int)+6 := by
              dsimp [Bg]
              omega

            have hrootEq :
                (↑(14*2^n-2*n-16):Int)+4*(↑(0:Nat):Int)+4*(n:Int)+20 =
                  14*(2:Int)^n+2*(n:Int)+4 := by
              have hnat : (14*2^n-2*n-16)+4*n+20=14*2^n+2*n+4 := by omega
              exact_mod_cast hnat
            have hpreModel :
                TwoRun ((2:Int)^n) (14*(2:Int)^n+2*(n:Int)+4)
                  ((n:Int)+6) s Wa Ba := by
              have hh := source_two_chain_model n s
                (14*2^n-2*n-16) 3 0 B0 D0 M0 pre hrootMass
              rw [hrootEq] at hh
              simpa [Wa,Ba] using hh
            have hmid1Model :
                TwoRun ((2:Int)^n) Wb (Ba+(alpha:Int)) u Wc Bc := by
              have hh := source_two_chain_model n u
                (2*k1-4) (c1+4) (M0+t1+1) B2 D2 M2 mid1 hmass1
              simpa [Wb,Wc,Bc,hB1] using hh
            have hmid2Model :
                TwoRun ((2:Int)^n) Wd (Bc+(beta:Int)) v We Be := by
              have hh := source_two_chain_model n v
                (2*k2-4) (c2+4) (M2+t2+1) B4 D4 M4 mid2 hmass3
              simpa [Wd,We,Be,hB2] using hh
            have hmid3Model :
                TwoRun ((2:Int)^n) Wf (Be+(gamma:Int)) w Wg Bg := by
              have hh := source_two_chain_model n w
                (2*k3-4) (c3+4) (M4+t3+1) B6 D6 M6 mid3 hmass5
              simpa [Wf,Wg,Bg,hB3] using hh
            have htailModel :
                TwoRun ((2:Int)^n) Wh (Bg+(delta:Int)) r Wj Bj := by
              have hh := source_two_chain_model n r
                (2*k4-4) (c4+4) (M6+t4+1) b d m tail4 hmass7
              simpa [Wh,Wj,Bj,hB4] using hh

            have hSh1Model :
                ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
                  I ((2:Int)^n) Wa Ba-(C1:Int)*(2:Int)^n+
                    (L1:Int)*Ba-(O1:Int) := by
              simpa [Wa,Ba,Wb] using hSh1
            have hSh2Model :
                ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
                  I ((2:Int)^n) Wc Bc-(C2:Int)*(2:Int)^n+
                    (L2:Int)*Bc-(O2:Int) := by
              simpa [Wc,Bc,Wd] using hSh2
            have hSh3Model :
                ((2:Int)^gamma)*I ((2:Int)^n) Wf (Be+(gamma:Int)) =
                  I ((2:Int)^n) We Be-(C3:Int)*(2:Int)^n+
                    (L3:Int)*Be-(O3:Int) := by
              simpa [We,Be,Wf] using hSh3
            have hSh4Model :
                ((2:Int)^delta)*I ((2:Int)^n) Wh (Bg+(delta:Int)) =
                  I ((2:Int)^n) Wg Bg-(C4:Int)*(2:Int)^n+
                    (L4:Int)*Bg-(O4:Int) := by
              simpa [Wg,Bg,Wh] using hSh4
            have hwallModel : Wj=12*(2:Int)^n := by
              dsimp [Wj]
              exact_mod_cast hwall
            exact no_four_shallow_model_from_source_coefficients
              n s u v w r t1 t2 t3 t4 alpha beta gamma delta
              C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 hn
              ht1 ht2 ht3 ht4 hpr1 hpr2 hpr3 hpr4
              Wa Ba Wb Wc Bc Wd We Be Wf Wg Bg Wh Wj Bj
              hpreModel hSh1Model hmid1Model hSh2Model hmid2Model
              hSh3Model hmid3Model hSh4Model htailModel hwallModel

/-- Every finite legal inverseAt trace restricted to depths 0,1,2 which
reaches the exact shifted wall at n>=76 has at least five shallow edges. -/
theorem source_low_trace_wall_needs_five_shallows
    (n z b d m : Nat) (hn : 76≤n)
    (h : SourceLowTrace n z (14*2^n-2*n-16) 3 0 b d m)
    (hwall : b+4*m+4*n+20=12*2^n) : 5≤z := by
  by_cases hfive : 5≤z
  · exact hfive
  · have hz4 : z≤4 := by omega
    have hn14 : 14≤n := by omega
    have hword := h.toWord
    rcases (by omega : z=0 ∨ z=1 ∨ z=2 ∨ z=3 ∨ z=4) with h0|h1|h2|h3|h4
    · subst z
      exact False.elim (source_low_word_zero_no_wall n b d m hn14 hword hwall)
    · subst z
      exact False.elim (source_low_word_one_no_wall n b d m hn14 hword hwall)
    · subst z
      exact False.elim (source_low_word_two_no_wall n b d m hn14 hword hwall)
    · subst z
      exact False.elim (source_low_word_three_no_wall n b d m hn14 hword hwall)
    · subst z
      exact False.elim (source_low_word_four_no_wall n b d m hn hword hwall)

#print axioms source_low_word_four_no_wall
#print axioms source_low_trace_wall_needs_five_shallows

end BB6.Agent43FourShallowSourceLift
