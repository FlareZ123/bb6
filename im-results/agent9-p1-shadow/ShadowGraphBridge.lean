import ShadowSourceStep
namespace BB6.Shadow
open BB6.Agent1Quarter

/-- Exact two-integer dyadic shadow graph of the original census. -/
inductive ShadowReach (L z0 : Nat) : Nat → Nat → Prop where
  | root : ShadowReach L z0 0 z0
  | step (m z t r zp : Nat)
      (h : ShadowReach L z0 m z)
      (hdiv : z=2^t*r)
      (hnext : 2*zp+1=L+m+t+r) :
      ShadowReach L z0 (m+t+1) zp

/-- All safely bounded original P1 odd inverse-cone nodes are in the
    compressed graph. This is a genuine source-to-shadow simulation. -/
theorem bounded_odd_cone_in_shadow_graph
    (N L b0 d0 w0 z0 alpha0 : Nat)
    (hrootmass : b0+d0+2*L+3=56*2^N)
    (hL : 8≤L)
    (hrootOff : L=w0+z0)
    (hrootW : 4≤w0) (hrootZ : 0<z0)
    (hrootEncoded : b0+4*w0=alpha0*2^N)
    (b d m : Nat) (hcone : OddCone b0 d0 b d m) :
    b%4=0 → m+2≤N →
    ∃ (w z alpha : Nat),
      ShadowReach L z0 m z ∧ 0<z ∧ 4≤w ∧ L+m=w+z ∧
      2^m*(b+4*w)=alpha*2^N := by
  induction hcone with
  | root =>
      intro hb4 hcost
      refine ⟨w0,z0,alpha0,ShadowReach.root,hrootZ,hrootW,?_,?_⟩
      · simpa using hrootOff
      · simpa using hrootEncoded
  | @parent bp dp mp t k c hprev hb hb4p hd hi hk hc ih =>
      intro hb4child hcost
      have hparentcost : mp+2≤N := by omega
      obtain ⟨w,z,alpha,hgraph,hzpos,hw4,hoff,hscaled⟩ :=
        ih hb4p hparentcost
      obtain ⟨r,zp,wp,alphap,hr,hnext,hzp,hwp,hwoff,halpha,hscaledp⟩ :=
        original_odd_shadow_step N L mp t bp dp w z alpha k c b0 d0
          hprev hrootmass hL hoff hw4 hzpos hscaled hb hb4p hd hi hc
          hk hb4child (by omega)
      have hgraphp : ShadowReach L z0 (mp+t+1) zp :=
        ShadowReach.step mp z t r zp hgraph hr hnext
      exact ⟨wp,zp,alphap,hgraphp,hzp,hwp,by omega,hscaledp⟩

#print axioms bounded_odd_cone_in_shadow_graph
end BB6.Shadow
