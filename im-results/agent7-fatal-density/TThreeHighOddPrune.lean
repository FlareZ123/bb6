import TThreeHighNatSource
import ForkOddDead27
set_option maxHeartbeats 0
namespace CascadeTranslatedRayDepth
open CascadeOddRay CascadeResetInverse CascadeForkOddDead27

private theorem power_dominates (n : Nat) (hn : 20≤n) : n≤2^(n-4) := by
  have h : ∀k:Nat, 20+k≤2^(16+k) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have he : 16+(k+1)=(16+k)+1:=by omega
      rw [he,Nat.pow_succ]
      omega
  have he1 : n=20+(n-20):=by omega
  have he2 : n-4=16+(n-20):=by omega
  simpa only [←he1, ←he2] using h (n-20)

private theorem power_prev (n : Nat) (hn:20≤n) : 2^(n-4)=2*2^(n-5) := by
  have he : n-4=(n-5)+1 := by omega
  calc
    2^(n-4)=2^((n-5)+1):=by rw [←he]
    _=2*2^(n-5):=by rw [Nat.pow_succ];omega

/-- Under exact high-q second-parent bounds, valuation-zero and valuation-one
    odd inverse images each lie in a source-excluded dyadic image gap. -/
theorem high_child_low_odd_gaps (n r : Nat) (hn:20≤n)
    (hlower:10934*((2^(n-4):Nat):Int)-961*(n:Int)+18609≤6561*(r:Int))
    (hupper:6561*(r:Int)≤10942*((2^(n-4):Nat):Int)-10177*(n:Int)+6321) :
    (∀u:Nat, 2*r+5=3*u → 2^(n-4)<u ∧ 2*u+2<3*2^(n-4)) ∧
    (∀u:Nat, 2*r+5=9*u → 2^(n-5)<2*u ∧ 2*(2*u)+2<3*2^(n-5)) := by
  have hp := power_dominates n hn
  have hpI : (n:Int)≤((2^(n-4):Nat):Int) := by exact_mod_cast hp
  have hpPrev := power_prev n hn
  have hpPrevI : ((2^(n-4):Nat):Int)=2*((2^(n-5):Nat):Int) := by
    exact_mod_cast hpPrev
  constructor
  · intro u hu
    have huI : (2:Int)*(r:Int)+5=3*(u:Int) := by exact_mod_cast hu
    constructor
    · have hlI : ((2^(n-4):Nat):Int)<(u:Int) := by omega
      exact_mod_cast hlI
    · have hhI : (2:Int)*(u:Int)+2<3*((2^(n-4):Nat):Int) := by omega
      exact_mod_cast hhI
  · intro u hu
    have huI : (2:Int)*(r:Int)+5=9*(u:Int) := by exact_mod_cast hu
    constructor
    · have hlI : ((2^(n-5):Nat):Int)<2*(u:Int) := by omega
      exact_mod_cast hlI
    · have hhI : (2:Int)*(2*(u:Int))+2<3*((2^(n-5):Nat):Int) := by omega
      exact_mod_cast hhI

/-- In the actual complete first-reset inverse grammar, the high-q
    second parent cannot have odd valuation zero or one. -/
theorem high_child_parent_low_odd_prune (n r a : Nat) (hn:20≤n)
    (hlower:10934*((2^(n-4):Nat):Int)-961*(n:Int)+18609≤6561*(r:Int))
    (hupper:6561*(r:Int)≤10942*((2^(n-4):Nat):Int)-10177*(n:Int)+6321)
    (hparent:ResetParent a r) :
    (∃k,(6*2^k-1≤r ∧ r≤8*2^k-3) ∧ 2*r=8*2^k+a+k) ∨
    (∃k t d,2≤t ∧ d%2=1 ∧
      (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
      2*r+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+a+k+5) := by
  obtain ⟨hzero,hone⟩ := high_child_low_odd_gaps n r hn hlower hupper
  rcases hparent with heven | ⟨k,t,d,hd,hband,hnum,heq⟩
  · exact Or.inl heven
  · by_cases ht0:t=0
    · subst t
      have heq0:2*r+5=3*d:=by simpa using hnum
      have hgap:=hzero d heq0
      have hb:(6*2^k+1≤d ∧ d≤8*2^k-1):=by simpa using hband
      exact False.elim ((gap_avoids_odd_images (n-4) d hgap.1 hgap.2) k hb)
    · by_cases ht1:t=1
      · subst t
        have heq1:2*r+5=9*d:=by simpa using hnum
        have hgap:=hone d heq1
        have hb:(6*2^k+1≤2*d ∧ 2*d≤8*2^k-1):=by simpa using hband
        exact False.elim ((gap_avoids_odd_images (n-5) (2*d) hgap.1 hgap.2) k hb)
      · exact Or.inr ⟨k,t,d,by omega,hd,hband,hnum,heq⟩

/-- Full source-connected high-q t=3 parent theorem, quantified over every exact first-reset predecessor. -/
theorem high_source_parent_low_odd_prune (n j d q e r a : Nat)
  (hn:20≤n)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d)
  (hrel:16*d=2^n+q+(n-3)+5)
  (hgate:2*q+5=81*e)
  (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
  (hparent:ResetParent a r) :
    (∃k,(6*2^k-1≤r ∧ r≤8*2^k-3) ∧ 2*r=8*2^k+a+k) ∨
    (∃k t d,2≤t ∧ d%2=1 ∧
      (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
      2*r+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+a+k+5) := by
  obtain ⟨hl,hu⟩ := high_source_ray_bounds n j d q e r hn hm hz hrel hgate hrrel
  exact high_child_parent_low_odd_prune n r a hn hl hu hparent

#print axioms high_child_low_odd_gaps
#print axioms high_child_parent_low_odd_prune
#print axioms high_source_parent_low_odd_prune
end CascadeTranslatedRayDepth
