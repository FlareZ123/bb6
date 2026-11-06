import UniformPrecisionPath
import ShadowSourceStep
import ShadowDepthBudgetSource
import OddConeMass

namespace BB6.Agent9Precision
open BB6.Agent1Quarter BB6.Shadow BB6.Agent9Budget BB6.Precision

/-- A source-authentic P1 odd inverse cone embeds in exact unbounded
    scalar shadow reachability. Only per-path budget and dyadic bounds
    are assumed, so no finite list of lifted nodes is required. -/
theorem genuine_cone_shadow_reach
    (K budget N L b0 d0 w0 zinit alpha0 : Nat)
    (hrootmass : b0+d0+2*L+3=56*2^N)
    (hL : 8≤L) (hbudget : budget+K+3≤N)
    (hrootOff : L=w0+zinit)
    (hrootW : 4≤w0) (hrootZ : 0<zinit)
    (hrootEncoded : b0+4*w0=alpha0*2^N)
    (hsmall : ∀ m z, ShadowReach L zinit m z → m≤budget)
    (hnodiv : ∀ m z, ShadowReach L zinit m z → ¬2^K ∣ z)
    (b d m : Nat) (hcone : OddCone b0 d0 b d m)
    (hb4 : b%4=0) :
    ∃ w z alpha,
      ShadowReach L zinit m z ∧ 0<z ∧ 4≤w ∧
      L+m=w+z ∧ 2^m*(b+4*w)=alpha*2^N := by
  induction hcone with
  | root =>
      exact ⟨w0,zinit,alpha0,ShadowReach.root,hrootZ,hrootW,
        by simpa using hrootOff,by simpa using hrootEncoded⟩
  | @parent bp dp mp t k c hprev hb hb4p hd hi hk hc ih =>
      obtain ⟨w,z,alpha,hpath,hz,hw,hoff,hscaled⟩ := ih hb4p
      have hmBudget : mp≤budget := hsmall mp z hpath
      have hmass0 := odd_cone_mass b0 d0 bp dp mp hprev
      have hmass : bp+dp+2*mp+2*L+3=56*2^N := by omega
      have hdepth := source_depth_le_K
        K N L mp bp dp w z alpha t k c
        hmass hoff hscaled (by omega) (by omega)
        (hnodiv mp z hpath) hi
      obtain ⟨r,zp,wp,alphap,hdiv,hnext,hzp,hwp,hwoff,halpha,hscaledp⟩ :=
        original_odd_shadow_step N L mp t bp dp w z alpha k c b0 d0
          hprev hrootmass hL hoff hw hz hscaled hb hb4p hd hi hc
          hk hb4 (by omega)
      have hpathp : ShadowReach L zinit (mp+t+1) zp :=
        ShadowReach.step hpath t r zp hdiv hnext
      exact ⟨wp,zp,alphap,hpathp,hzp,hwp,by omega,hscaledp⟩

#print axioms genuine_cone_shadow_reach
end BB6.Agent9Precision
