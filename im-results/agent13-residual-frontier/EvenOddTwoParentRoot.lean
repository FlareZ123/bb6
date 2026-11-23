import EvenOddSmallValuation
import M0EvenEvenSumZero
import SixForcedNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13TwoParent
open BB6.Agent46

/-- The only two original-source candidate parents of a sufficiently
    large even/odd state outside the 64-divisible valuation sector. -/
def parentLeft (x y n : Nat) : Nat :=
  (x+y+1)/(2^(n+1))-3

def parentRight (x y n : Nat) : Nat :=
  (x+2*y-parentLeft x y n-(7+3*n))/2

private theorem candidate_parent_eq
    (a k x y n : Nat)
    (hn : n=0 ∨ n=2)
    (hlow : a<2*k)
    (hpow : x+y+1=2^n*(2*(a-1)+8))
    (hcost : (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2)
    (hbig : 64≤x+y+1) :
    a=parentLeft x y n ∧ k=parentRight x y n := by
  have ha2 : 2≤a := by
    rcases hn with h0|h2
    · subst n
      simp at hpow
      omega
    · subst n
      simp at hpow
      omega
  have ha : a=parentLeft x y n := by
    rcases hn with h0|h2
    · subst n
      simp [parentLeft] at *
      omega
    · subst n
      simp [parentLeft] at *
      omega
  have hk : k=parentRight x y n := by
    unfold parentRight
    rw [←ha]
    rcases hn with h0|h2
    · subst n
      simp at hcost ⊢
      omega
    · subst n
      simp at hcost ⊢
      omega
  exact ⟨ha,hk⟩

/-- General reusable two-parent blank-root sieve.
    No quotient certificate is needed: if the two complete original
    inverse parents both normalize into the already source-certified
    odd-image forbidden region, the target is globally unreachable. -/
theorem two_parent_normalizer_excluded
    (x y : Nat)
    (hx : 5<x)
    (hxe : x%2=0) (hyo : y%2=1)
    (hy : 5≤y)
    (hbig : 64≤x+y+1)
    (hn64 : (x+y+1)%64≠0)
    (h0 : BB6.Agent11SixForced.sixForcedExcluded
       (parentLeft x y 0) (parentRight x y 0)=true)
    (h2 : BB6.Agent11SixForced.sixForcedExcluded
       (parentLeft x y 2) (parentRight x y 2)=true) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
       x y hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13SmallFan.even_odd_small_valuation_parent
      a k x y hxe hyo hy hbig hn64 hedge
  obtain ⟨ha,hk⟩ := candidate_parent_eq
    a k x y n hn hlow hpow hcost hbig
  rw [ha,hk] at hpre
  rcases hn with hn0|hn2
  · subst n
    exact (BB6.Agent11SixForced.sixForcedExcluded_sound
      (parentLeft x y 0) (parentRight x y 0) h0) hpre
  · subst n
    exact (BB6.Agent11SixForced.sixForcedExcluded_sound
      (parentLeft x y 2) (parentRight x y 2) h2) hpre

/-- A source-only parent sieve in which the two candidate parents may
    be rejected by *any* accepted source theorem, not just the six-sector
    normalizer Boolean. -/
theorem two_parent_nonreach
    (x y : Nat)
    (hx : 5<x) (hxe : x%2=0) (hyo : y%2=1)
    (hy : 5≤y) (hbig : 64≤x+y+1)
    (hn64 : (x+y+1)%64≠0)
    (h0 : ¬ BB6.Agent3.CReach
      (parentLeft x y 0) (parentRight x y 0))
    (h2 : ¬ BB6.Agent3.CReach
      (parentLeft x y 2) (parentRight x y 2)) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13SmallFan.even_odd_small_valuation_parent
      a k x y hxe hyo hy hbig hn64 hedge
  obtain ⟨ha,hk⟩ := candidate_parent_eq
    a k x y n hn hlow hpow hcost hbig
  rw [ha,hk] at hpre
  rcases hn with hn0|hn2
  · subst n
    exact h0 hpre
  · subst n
    exact h2 hpre

/-- Original-source blank-image invariant: the odd-right sector can only
    be reached with sum congruent to zero or three modulo four. -/
theorem odd_forbidden_image (x y : Nat)
    (hy : 5≤y) (hyo : y%2=1)
    (hsum : (x+y)%4=1 ∨ (x+y)%4=2) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at ht
    omega
  | succ n =>
    have hi := BB6.Agent3.blank_section_odd_image
      n x y ht hy hyo
    rcases hsum with h1|h2 <;> omega

#print axioms two_parent_nonreach
#print axioms odd_forbidden_image

#print axioms two_parent_normalizer_excluded
end BB6.Agent13TwoParent
