import ShadowSourceStep
import ShadowQ29DepthSource
import OddConeMass

namespace BB6.Shadow
open BB6.Agent1Quarter

/-- A finite closed shadow invariant with a small m-coordinate
    automatically traps the entire original P1 odd inverse cone,
    without any a priori inverse-cost budget. -/
theorem finite_shadow_invariant_lifts_full_cone
    (N L b0 d0 w0 z0 alpha0 : Nat)
    (nodes : List (Nat × Nat))
    (hrootmass : b0+d0+2*L+3=56*2^N)
    (hL : 8≤L) (hN : 21≤N)
    (hrootOff : L=w0+z0)
    (hrootW : 4≤w0) (hrootZ : 0<z0)
    (hrootEncoded : b0+4*w0=alpha0*2^N)
    (hrootIn : (0,z0) ∈ nodes)
    (hclosed : ∀ m z t r zp,
      (m,z) ∈ nodes → z=2^t*r →
      2*zp+1=L+m+t+r → (m+t+1,zp) ∈ nodes)
    (hsmall : ∀ m z, (m,z) ∈ nodes → m≤10)
    (hnodiv : ∀ m z, (m,z) ∈ nodes → ¬256 ∣ z)
    (b d m : Nat) (hcone : OddCone b0 d0 b d m) :
    b%4=0 →
    ∃ w z alpha,
      (m,z)∈nodes ∧ 0<z ∧ 4≤w ∧ L+m=w+z ∧
      2^m*(b+4*w)=alpha*2^N := by
  induction hcone with
  | root =>
      intro h4
      refine ⟨w0,z0,alpha0,hrootIn,hrootZ,hrootW,?_,?_⟩
      · simpa using hrootOff
      · simpa using hrootEncoded
  | @parent bp dp mp t k c hprev hb hb4p hd hi hk hc ih =>
      intro hchild
      obtain ⟨w,z,alpha,hmember,hz,hw,hoff,hscaled⟩ := ih hb4p
      have hm10 : mp≤10 := hsmall mp z hmember
      have hmass0 := odd_cone_mass b0 d0 bp dp mp hprev
      have hmass : bp+dp+2*mp+2*L+3=56*2^N := by omega
      have hdepth := source_depth_le8_mod256
        N L mp bp dp w z alpha t k c
        hmass hoff hscaled (by omega) (by omega)
        (hnodiv mp z hmember) hi
      obtain ⟨r,zp,wp,alphap,hdiv,hnext,hzp,hwp,hwoff,halpha,hscaledp⟩ :=
        original_odd_shadow_step N L mp t bp dp w z alpha k c b0 d0
          hprev hrootmass hL hoff hw hz hscaled hb hb4p hd hi hc
          hk hchild (by omega)
      have hmemberp := hclosed mp z t r zp hmember hdiv hnext
      exact ⟨wp,zp,alphap,hmemberp,hzp,hwp,by omega,hscaledp⟩

#print axioms finite_shadow_invariant_lifts_full_cone
end BB6.Shadow
