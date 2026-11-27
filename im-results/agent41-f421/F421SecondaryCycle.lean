import F421SecondaryWords

namespace BB6Coverage.Agent41F421.EpochWords
open Agent31Pump
open Regular (P Q Z R)
open F421TertiaryGuard (drain QBudget)

/-- Exact positive secondary cycle with arbitrary guarded terminal deletions. -/
theorem secondaryCycleSource (a b x y : Nat) (cs as bs ds : List PC) (cB : PC)
    (lo hi : List TC) (c : TC) (U : List Bool) (A B C rA rB rC : Nat)
    (hb : 2≤b) (hx : 2≤x) (hy : 2≤y) (hv : valid cs)
    (hxs : svalid (lo++c::hi)) (hlo : clear lo) (hz : ∀ t∈lo, 2≤t.z)
    (hc : c.f=true) (hcz : 1≤c.z) (hcr : 1≤c.r) (hhi : svalid hi)
    (gA : guarded 0 (dec cs)) (eA : drain 0 0 (dec cs)=(as,A,rA)) (vA : valid as)
    (gB : guarded 0 (crossFar (b+1+A+rA) (x-1) as))
    (eB : drain 0 0 (crossFar (b+1+A+rA) (x-1) as)=(cB::bs,B,rB)) (vB : valid (cB::bs))
    (gC : guarded 0 (crossFar (a+2+2*A+1+B+rB) cB.p bs))
    (eC : drain 0 0 (crossFar (a+2+2*A+1+B+rB) cB.p bs)=(ds,C,rC)) :
    reaches (1+A+1+B+1+C) (sbody a b x y cs (lo++c::hi) U)
      (sbody (1+2*C) (1+2*B+1+C+rC) cB.q (y-1) ds (sTouch lo++sTarget c::hi) U) := by
  have h1 := sFirst a b x y cs (lo++c::hi) U hb (by omega) hv
  have h2 := drainReach (a+2) (b+1) (dec cs) as A rA
    (rep P (x-1)++Q++rep P y++stail (lo++c::hi) U) (by omega) gA eA
  have h3 := sSecond (a+2+2*A) (b+1+A+rA) x y as (lo++c::hi) U (by omega) hx (by omega) vA hxs
  have h4 := drainReach 1 (a+2+2*A+1) _ (cB::bs) B rB
    (P++rep Q (y-1)++sshift (lo++c::hi)++[false]++U) (by omega) gB eB
  have h5 := sThird (1+2*B) (a+2+2*A+1+B+rB) y cB bs lo hi c U (by omega) hy vB hlo hz hc hcz hcr hhi
  have h6 := drainReach 1 (1+2*B+1) _ ds C rC
    (rep P cB.q++Z++rep P (y-1)++stail (sTouch lo++sTarget c::hi) U) (by omega) gC eC
  simp only [rep,List.append_nil,List.append_assoc] at h1 h2 h3 h4 h5 h6
  unfold sbody at h1 ⊢
  simp only [List.append_assoc] at h1 ⊢
  exact reachesTrans (reachesTrans (reachesTrans (reachesTrans (reachesTrans h1 h2) h3) h4) h5) h6

/-- Secondary tail guard: a row can pay for every remaining nonterminal visit. -/
def stailGood : List TC → Prop
  | [] => True
  | c::cs => 2≤c.z ∧ counter cs+2≤c.r ∧ stailGood cs

theorem stailValid (xs : List TC) (hg : stailGood xs) : ∀ c∈xs, 2≤c.z ∧ 2≤c.r := by
  induction xs with
  | nil => simp
  | cons c cs ih =>
    rcases hg with ⟨hz,hr,ht⟩
    intro t hm; rcases List.mem_cons.mp hm with rfl|hm
    · omega
    · exact ih ht t hm

theorem sDecrement (xs : List TC) (hg : stailGood xs) (hpos : 0<counter xs) :
    ∃ lo c hi, xs=lo++c::hi ∧ clear lo ∧ c.f=true ∧
      stailGood (sTouch lo++sTarget c::hi) ∧ counter (sTouch lo++sTarget c::hi)+1=counter xs := by
  induction xs with
  | nil => simp [counter] at hpos
  | cons d ds ih =>
    rcases hg with ⟨hz,hr,ht⟩
    cases hf : d.f
    · have hpos' : 0<counter ds := by simp [counter,bit,hf] at hpos; omega
      obtain ⟨lo,c,hi,he,hcl,hc,hg',hc'⟩ := ih ht hpos'
      refine ⟨d::lo,c,hi,by simp [he],?_,hc,?_,?_⟩
      · intro z h; rcases List.mem_cons.mp h with rfl|h
        · exact hf
        · exact hcl z h
      · change stailGood (⟨d.z,d.r-1,true⟩::(sTouch lo++sTarget c::hi))
        refine ⟨hz,?_,hg'⟩
        change counter (sTouch lo++sTarget c::hi)+2≤d.r-1
        rw [he] at hr hc'
        omega
      · change counter (⟨d.z,d.r-1,true⟩::(sTouch lo++sTarget c::hi))+1=counter (d::ds)
        simp [counter,bit,hf]; omega
    · refine ⟨[],d,ds,rfl,by simp [clear],hf,?_,?_⟩
      · change stailGood (sTarget d::ds)
        exact ⟨by change 2≤d.z+1; omega,hr,ht⟩
      · simp [sTouch,sTarget,counter,bit,hf,Nat.add_comm]

#print axioms secondaryCycleSource
#print axioms sDecrement
end BB6Coverage.Agent41F421.EpochWords
