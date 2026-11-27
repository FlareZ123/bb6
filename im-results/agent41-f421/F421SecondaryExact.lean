import F421SecondaryEpoch

namespace BB6Coverage.Agent41F421.EpochWords

/-- Arithmetic endpoint of the entire primary countdown. -/
def sIter : Nat → Nat × Nat × List PC → Nat × Nat × List PC
  | 0, p => p
  | k+1, (_,b,cs) => sIter k (sNext b cs)

/-- At zero every original secondary bit is clear. Its former suffix count
    is exactly the number of borrows; the original bit adds one extra carry. -/
def sTailFinal : List TC → List TC
  | [] => []
  | c::cs => ⟨c.z+counter cs+bit c.f,c.r-counter cs,false⟩::sTailFinal cs

theorem sTailFinalDecrement (lo hi : List TC) (c : TC) (hc : c.f=true) (hl : clear lo)
    (hg : stailGood (lo++c::hi)) (hcount : counter (sTouch lo++sTarget c::hi)+1=counter (lo++c::hi)) :
    sTailFinal (sTouch lo++sTarget c::hi)=sTailFinal (lo++c::hi) := by
  induction lo with
  | nil => simp [sTailFinal,sTouch,sTarget,bit,hc]; omega
  | cons d ds ih =>
    have hd := hl d (by simp)
    have hh : clear ds := fun t ht => hl t (by simp [ht])
    have hh' : stailGood (ds++c::hi) := hg.2.2
    have he : counter (sTouch ds++sTarget c::hi)+1=counter (ds++c::hi) := by
      simp [sTouch,counter,bit,hd] at hcount
      change 1+2*counter (sTouch ds++sTarget c::hi)+1=2*counter (ds++c::hi) at hcount
      omega
    have hr : counter (ds++c::hi)+2≤d.r := hg.2.1
    simp only [sTouch,List.map_cons,List.cons_append,sTailFinal,hd,bit,if_false,if_true,Nat.add_zero]
    change ⟨d.z+counter (sTouch ds++sTarget c::hi)+1,d.r-1-counter (sTouch ds++sTarget c::hi),false⟩::sTailFinal (sTouch ds++sTarget c::hi) = _
    rw [ih hh hh' he]
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
    congr 2 <;> omega

theorem sTailFinalZero (xs : List TC) (hc : counter xs=0) : sTailFinal xs=xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hf := zeroClear (c::cs) hc c (by simp)
    have hc' : counter cs=0 := by simp [counter,bit,hf] at hc; omega
    cases c
    simp_all [sTailFinal,bit]

/-- The source endpoint is the exact deterministic arithmetic state, rather
    than an existential state characterized only by a guard. -/
theorem secondaryEpochExact (n a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool)
    (hp : sPrimary n a b cs) (hx : n+3≤x) (hy : n+2≤y) (hc : counter xs=n) (hg : stailGood xs) :
    let (a',b',ds) := sIter n (a,b,cs)
    sPrimary 0 a' b' ds ∧ clear (sTailFinal xs) ∧ stailGood (sTailFinal xs) ∧ (sTailFinal xs).length=xs.length ∧
      reaches n (sbody a b x y cs xs U) (sbody a' b' (x-n) (y-n) ds (sTailFinal xs) U) := by
  induction n generalizing a b x y cs xs with
  | zero =>
    simp only [sIter,Nat.sub_zero]
    rw [sTailFinalZero xs hc]
    exact ⟨hp,zeroClear xs hc,hg,rfl,⟨0,by decide,rfl⟩⟩
  | succ n ih =>
    obtain ⟨lo,c,hi,he,hclear,hf,hg',hc'⟩ := sDecrement xs hg (by omega)
    rw [he] at hc hc' hg ⊢
    have hs := secondaryPrimaryCycleExact n a b x y cs lo hi c U hp (by omega) (by omega) hg hclear hf
    rcases hn : sNext b cs with ⟨a1,b1,cs1⟩
    rw [hn] at hs
    have hcount : counter (sTouch lo++sTarget c::hi)=n := by omega
    have ihResult := ih a1 b1 (x-1) (y-1) cs1 (sTouch lo++sTarget c::hi) hs.1 (by omega) (by omega) hcount hg'
    rcases hfin : sIter n (a1,b1,cs1) with ⟨a2,b2,ds⟩
    rw [hfin] at ihResult
    rw [sTailFinalDecrement lo hi c hf hclear hg hc'] at ihResult
    simp only [sIter,hn,hfin]
    refine ⟨ihResult.1,ihResult.2.1,ihResult.2.2.1,?_,?_⟩
    · simpa [sTouch] using ihResult.2.2.2.1
    · have h := reachesTrans hs.2 ihResult.2.2.2.2
      simpa only [show 1+n=n+1 by omega,show x-1-n=x-(n+1) by omega,show y-1-n=y-(n+1) by omega] using h

#print axioms secondaryEpochExact
end BB6Coverage.Agent41F421.EpochWords
