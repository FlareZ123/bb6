import F421SecondaryInduction

namespace BB6Coverage.Agent41F421.EpochWords

/-- Complete guarded secondary countdown for a mixed P-budget/divisibility primary. -/
theorem secondaryEpoch (n a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool)
    (hp : sPrimary n a b cs) (hx : n+3≤x) (hy : n+2≤y) (hc : counter xs=n) (hg : stailGood xs) :
    ∃ a' b' ds ys, sPrimary 0 a' b' ds ∧ clear ys ∧ stailGood ys ∧ ys.length=xs.length ∧
      reaches n (sbody a b x y cs xs U) (sbody a' b' (x-n) (y-n) ds ys U) := by
  induction n generalizing a b x y cs xs with
  | zero =>
    refine ⟨a,b,cs,xs,hp,zeroClear xs hc,hg,rfl,?_⟩
    simp only [Nat.sub_zero]; exact ⟨0,by decide,rfl⟩
  | succ n ih =>
    obtain ⟨lo,c,hi,he,hclear,hf,hg',hc'⟩ := sDecrement xs hg (by omega)
    rw [he] at hc hc' hg ⊢
    obtain ⟨a1,b1,cs1,hp1,hs⟩ := secondaryPrimaryCycle n a b x y cs lo hi c U hp (by omega) (by omega) hg hclear hf
    have hcount : counter (sTouch lo++sTarget c::hi)=n := by omega
    obtain ⟨a2,b2,ds,ys,hp2,hcl,hg2,hlen,ht⟩ := ih a1 b1 (x-1) (y-1) cs1 (sTouch lo++sTarget c::hi) hp1 (by omega) (by omega) hcount hg'
    refine ⟨a2,b2,ds,ys,hp2,hcl,hg2,by simpa [sTouch] using hlen,?_⟩
    have h := reachesTrans hs ht
    simpa only [show 1+n=n+1 by omega,show x-1-n=x-(n+1) by omega,show y-1-n=y-(n+1) by omega] using h

def firstPrimary : List PC := [⟨2883545,131073⟩,⟨7077811,2883586⟩,⟨2621288,3145735⟩,⟨224,3148774⟩,⟨960,3054⟩,⟨384,3038⟩,⟨2816,4031⟩,⟨3584,3967⟩,⟨512,767⟩,⟨2048,1535⟩]
def firstTail : List TC := [⟨32776,851959,false⟩,⟨16387,557051,true⟩,⟨860160,737276,true⟩,⟨659454,778236,true⟩,⟨2048,241660,false⟩,⟨62463,219134,true⟩,⟨63998,89087,true⟩,⟨48382,101116,true⟩,⟨1662,12415,true⟩,⟨1854,27260,true⟩,⟨926,8508,true⟩,⟨847,8620,true⟩,⟨1958,3527,true⟩,⟨1106,2529,true⟩,⟨41,2621,true⟩]

theorem firstPrimaryGood : sPrimary 32750 2047 3071 firstPrimary := by
  unfold sPrimary firstPrimary
  refine ⟨by decide,by decide,?_,by simp [F421TertiaryGuard.QBudget],by decide⟩
  simp only [sPGood]
  refine ⟨Or.inl (by decide),Or.inl (by decide),?_⟩
  refine ⟨Or.inr ⟨by decide,327661,by decide,by decide⟩,?_⟩
  refine ⟨Or.inr ⟨by decide,14,by decide,by decide⟩,?_⟩
  refine ⟨Or.inr ⟨by decide,30,by decide,by decide⟩,?_⟩
  refine ⟨Or.inr ⟨by decide,6,by decide,by decide⟩,?_⟩
  refine ⟨Or.inr ⟨by decide,22,by decide,by decide⟩,?_⟩
  refine ⟨Or.inr ⟨by decide,14,by decide,by decide⟩,?_⟩
  refine ⟨Or.inr ⟨by decide,1,by decide,by decide⟩,?_⟩
  exact ⟨Or.inr ⟨by decide,2,by decide,by decide⟩,trivial⟩

theorem firstSecondaryEpoch (U : List Bool) :
    ∃ a' b' ds ys, sPrimary 0 a' b' ds ∧ clear ys ∧ stailGood ys ∧ ys.length=15 ∧
      reaches 32750 (sbody 2047 3071 1703916 262124 firstPrimary firstTail U) (sbody a' b' 1671166 229374 ds ys U) := by
  have h := secondaryEpoch 32750 2047 3071 1703916 262124 firstPrimary firstTail U firstPrimaryGood (by decide) (by decide) (by decide) (by simp [stailGood,firstTail,counter,bit])
  exact h

#print axioms secondaryEpoch
#print axioms firstSecondaryEpoch
end BB6Coverage.Agent41F421.EpochWords
