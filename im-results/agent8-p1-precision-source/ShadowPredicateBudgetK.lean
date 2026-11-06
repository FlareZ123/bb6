import ShadowSourceStep
import ShadowDepthBudgetSource
import OddConeMass

namespace BB6.Agent8PrecisionSource
open BB6.Agent1Quarter BB6.Shadow BB6.Agent9Budget

/-- Authentic P1 odd-inverse shadow containment in an arbitrary predicate.
This supports infinite cost-graded 2-adic shadow languages without enumeration. -/
theorem source_oddcone_predicate_shadow
    (K budget N L b0 d0 w0 z0 alpha0 : Nat)
    (S : Nat → Nat → Prop)
    (hrootmass : b0+d0+2*L+3=56*2^N)
    (hL : 8≤L) (hbudget : budget+K+3≤N)
    (hrootOff : L=w0+z0)
    (hrootW : 4≤w0) (hrootZ : 0<z0)
    (hrootEncoded : b0+4*w0=alpha0*2^N)
    (hrootIn : S 0 z0)
    (hclosed : ∀ m z t v zp,
      S m z → z=2^t*v →
      2*zp+1=L+m+t+v → S (m+t+1) zp)
    (hsmall : ∀ m z, S m z → m≤budget)
    (hnodiv : ∀ m z, S m z → ¬2^K ∣ z)
    (b d m : Nat) (hcone : OddCone b0 d0 b d m) :
    b%4=0 →
    ∃ w z alpha,
      S m z ∧ 0<z ∧ 4≤w ∧ L+m=w+z ∧
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
      have hmBudget : mp≤budget := hsmall mp z hmember
      have hmass0 := odd_cone_mass b0 d0 bp dp mp hprev
      have hmass : bp+dp+2*mp+2*L+3=56*2^N := by omega
      have hdepth := source_depth_le_K
        K N L mp bp dp w z alpha t k c
        hmass hoff hscaled (by omega) (by omega)
        (hnodiv mp z hmember) hi
      obtain ⟨r,zp,wp,alphap,hdiv,hnext,hzp,hwp,hwoff,halpha,hscaledp⟩ :=
        original_odd_shadow_step N L mp t bp dp w z alpha k c b0 d0
          hprev hrootmass hL hoff hw hz hscaled hb hb4p hd hi hc
          hk hchild (by omega)
      have hmemberp := hclosed mp z t r zp hmember hdiv hnext
      exact ⟨wp,zp,alphap,hmemberp,hzp,hwp,by omega,hscaledp⟩

#print axioms source_oddcone_predicate_shadow
end BB6.Agent8PrecisionSource
