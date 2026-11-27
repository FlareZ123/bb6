import F421EpochInduction

namespace BB6Coverage.Agent41F421.EpochWords

def counter : List TC → Nat
  | [] => 0
  | c::cs => bit c.f+2*counter cs

def tailGood : List TC → Prop
  | [] => True
  | c::cs => counter (c::cs)+2≤c.z ∧ 2≤c.r ∧ tailGood cs

theorem tailValidOf (xs : List TC) (hg : tailGood xs) : tailValid xs := by
  induction xs with
  | nil => simp [tailValid]
  | cons c cs ih =>
    rcases hg with ⟨hz,hr,ht⟩
    intro z hz'
    rcases List.mem_cons.mp hz' with rfl|hz'
    · omega
    · exact ih ht z hz'

theorem zeroClear (xs : List TC) (h : counter xs=0) : clear xs := by
  induction xs with
  | nil => simp [clear]
  | cons c cs ih =>
    have hc : c.f=false := by cases hf : c.f <;> simp [counter,bit,hf] at h ⊢
    have ht : counter cs=0 := by simp [counter,bit,hc] at h; omega
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact hc
    · exact ih ht z hz

theorem tailDecrease (xs : List TC) (hg : tailGood xs) (hpos : 0<counter xs) :
    ∃ lo c hi, xs=lo++c::hi ∧ clear lo ∧ tailValid lo ∧ c.f=true ∧ 1≤c.z ∧
      tailGood (touch lo++target c::hi) ∧ counter (touch lo++target c::hi)+1=counter xs := by
  induction xs with
  | nil => simp [counter] at hpos
  | cons d ds ih =>
    rcases hg with ⟨hz,hr,ht⟩
    cases hf : d.f
    · have hpos' : 0<counter ds := by simp [counter,bit,hf] at hpos; omega
      obtain ⟨lo,c,hi,he,hc,hv,hf',hz',hg',hc'⟩ := ih ht hpos'
      refine ⟨d::lo,c,hi,by simp [he],?_,?_,hf',hz',?_,?_⟩
      · intro z h; rcases List.mem_cons.mp h with rfl|h
        · exact hf
        · exact hc z h
      · intro z h; rcases List.mem_cons.mp h with rfl|h
        · omega
        · exact hv z h
      · change tailGood (⟨d.z-1,d.r,true⟩::(touch lo++target c::hi))
        refine ⟨?_,hr,hg'⟩
        simp [counter,bit,hf] at hz ⊢
        omega
      · change counter (⟨d.z-1,d.r,true⟩::(touch lo++target c::hi))+1=counter (d::ds)
        simp [counter,bit,hf]
        omega
    · refine ⟨[],d,ds,rfl,by simp [clear],by simp [tailValid],hf,by omega,?_,?_⟩
      · change tailGood (target d::ds)
        refine ⟨?_,by change 2≤d.r+1; omega,ht⟩
        simp [counter,target,bit,hf] at hz ⊢
        omega
      · simp [touch,target,counter,bit,hf,Nat.add_comm]

/-- A whole positive tertiary countdown, parameterized by its initial value.
    No simulation length or bounded-head assumption occurs in this theorem. -/
theorem tertiaryEpoch (n a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool)
    (hp : primary n a b cs) (hx : 3≤x) (hy : n+2≤y) (hc : counter xs=n) (hg : tailGood xs) :
    ∃ a' b' ds ys, primary 0 a' b' ds ∧ clear ys ∧ tailGood ys ∧
      reaches n (body a b x y cs xs U) (body a' b' (x+n) (y-n) ds ys U) := by
  induction n generalizing a b x y cs xs with
  | zero =>
    refine ⟨a,b,cs,xs,hp,zeroClear xs hc,hg,?_⟩
    simp only [Nat.add_zero,Nat.sub_zero]
    exact ⟨0,by decide,rfl⟩
  | succ n ih =>
    obtain ⟨lo,c,hi,he,hclear,hvalid,hf,hz,hg',hc'⟩ := tailDecrease xs hg (by omega)
    rw [he] at hc hc' ⊢
    obtain ⟨a1,b1,cs1,hp1,hs⟩ := primaryCycle n a b x y cs lo hi c U hp hx (by omega) hvalid hclear hf hz
    have hcount : counter (touch lo++target c::hi)=n := by omega
    obtain ⟨a2,b2,ds,ys,hp2,hcl,hg2,ht⟩ := ih a1 b1 (x+1) (y-1) cs1 (touch lo++target c::hi) hp1 (by omega) (by omega) hcount hg'
    refine ⟨a2,b2,ds,ys,hp2,hcl,hg2,?_⟩
    have h := reachesTrans hs ht
    simpa only [show 1+n=n+1 by omega,show x+1+n=x+(n+1) by omega,show y-1-n=y-(n+1) by omega] using h

#print axioms tailDecrease
#print axioms tertiaryEpoch
end BB6Coverage.Agent41F421.EpochWords
