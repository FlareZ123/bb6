import F421ZeroWords

namespace BB6Coverage.Agent41F421.EpochWords
open F421TertiaryGuard (drain QBudget Marked8 Survives8)

theorem strictCrossOne (b x B : Nat) (cs : List PC) (hx : 3≤x) (hp : pLower 3 cs)
    (hq : QBudget 1 (2*B) cs) (hb : 2*B*2^cs.length+2≤b) : strictBudget B (crossDirect b x cs) := by
  induction cs generalizing x B with
  | nil => simp [crossDirect,strictBudget] at hb ⊢; omega
  | cons c cs ih =>
    rcases hq with ⟨hc,ht⟩
    have hc' := hp c (by simp)
    have hpow : 2*(2*B)*2^cs.length=2*B*2^(cs.length+1) := by rw [Nat.pow_succ]; ac_rfl
    have hb' : 2*(2*B)*2^cs.length+2≤b := by rw [hpow]; simpa using hb
    refine ⟨by change 2*B+2≤c.q; omega,by change 2≤x-1; omega,?_⟩
    exact ih c.p (2*B) hc' (fun z hz => hp z (by simp [hz])) ht hb'

theorem finishQBudget (B : Nat) (cs : List PC) (hg : strictBudget B cs) : QBudget 1 B (strictFinish B cs) := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih =>
    exact ⟨by change 2+1*B≤c.q+B; have hq := hg.2.1; omega,ih (2*B) hg.2.2⟩

/-- Zero boundary after any positive tertiary epoch with one spare primary budget unit. -/
theorem primaryZero (a b x y z r v : Nat) (cs : List PC) (xs : List TC) (V : List Bool)
    (hg : primary 1 a b cs) (hx : 3≤x) (hy : 2≤y) (hr : 1≤r)
    (hxs : tailValid xs) (hcl : clear xs) :
    ∃ a' b' ds, a'=2*2^ds.length-1 ∧ 3*2^ds.length-1≤b' ∧ pLower 3 ds ∧ QBudget 1 1 ds ∧ 3≤ds.length ∧
      reaches 1 (body a b x y cs xs (zeroSuffix z r v V)) (secBody a' b' x y z r v ds xs V) := by
  rcases hg with ⟨ha,hb,hp,d0,d1,d2,hs,rfl,h0,h1,h2,hmod⟩
  have hp0 := hp d0 (by simp)
  have hp1 := hp d1 (by simp)
  have hp2 := hp d2 (by simp)
  have hph : pLower 3 hs := fun t ht => hp t (by simp [ht])
  have hv : valid (d0::d1::d2::hs) := by
    intro t ht
    have ht' := hp t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl|rfl|rfl|ht
    · exact ⟨by omega,by omega⟩
    · exact ⟨by omega,by omega⟩
    · exact ⟨by omega,by omega⟩
    · have hh := hmod t ht; exact ⟨by omega,by omega⟩
  let ah := crossDirect b d2.p hs
  let u0 : PC := ⟨d0.q,x-1⟩
  let u1 : PC := ⟨d1.q,d0.p-1⟩
  let u2 : PC := ⟨d2.q,d1.p-1⟩
  have eCross : crossFar b x (d0::d1::d2::hs)=u0::u1::u2::ah := by rw [crossFarEq]; rfl
  have hQa : QBudget 0 1 (u0::u1::u2::ah) := by rw [←eCross,crossFarEq]; exact crossQ b x 1 _ hx hp
  have hmA : Marked8 ah := crossMarked b d2.p hs hb hmod
  have gA : guarded 0 (u0::u1::u2::ah) := by
    apply guard3
    · dsimp [u0]; omega
    · dsimp [u1]; omega
    · dsimp [u2]; omega
    · dsimp [u0]; omega
    · dsimp [u1]; omega
    · dsimp [u2]; omega
    · exact markedGuard ah 7 8 0 hmA (crossQ b d2.p 8 hs hp2 hph)
  rcases eAh : drain 7 0 ah with ⟨as,A,rA⟩
  let v0 : PC := ⟨u0.p-1,u0.q+1⟩
  let v1 : PC := ⟨u1.p-3,u1.q+2⟩
  let v2 : PC := ⟨u2.p-7,u2.q+4⟩
  have eA : drain 0 0 (u0::u1::u2::ah)=(v0::v1::v2::as,A,rA) := by
    rw [drain3 u0 u1 u2 ah (by dsimp [u0]; omega) (by dsimp [u1]; omega) (by dsimp [u2]; omega),eAh]
  have modA := F421TertiaryGuard.drainMod8 ah 7 0 (by decide) hmA
  rw [eAh] at modA
  obtain ⟨hmAs,hAm⟩ := modA
  have qA := F421TertiaryGuard.drainQ (u0::u1::u2::ah) 0 1 1 0 0 (by decide) (by decide) hQa
  rw [eA] at qA
  obtain ⟨hQA,hLA,hAcount⟩ := qA
  have pA : pLower 3 (v0::v1::v2::as) := by
    exact pLowerCons 3 v0 _ (by dsimp [v0,u0]; omega)
      (pLowerCons 3 v1 _ (by dsimp [v1,u1]; omega)
      (pLowerCons 3 v2 _ (by dsimp [v2,u2]; omega) (survivesLower as hmAs)))
  have validA := validOf _ pA 1 1 hQA
  let N := 2^(v0::v1::v2::as).length
  let M := 2^(d0::d1::d2::hs).length
  have lenA : (v0::v1::v2::as).length≤(d0::d1::d2::hs).length+1 := by
    rw [←eCross,crossLength] at hLA; exact hLA
  have hnM : N≤2*M := by
    have hh := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) lenA
    simpa [N,M,Nat.pow_succ,Nat.mul_comm] using hh
  have hnPos : 0<N := Nat.pow_pos (by decide)
  have hN8 : 8≤N := by
    have hh := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (show 3≤(v0::v1::v2::as).length by simp)
    exact hh
  let bA := a+1+A+rA
  let ss := v1::v2::as
  have hBudgetC : strictBudget 1 (crossDirect bA v0.p ss) := by
    apply strictCrossOne
    · exact pA v0 (by simp)
    · exact fun t ht => pA t (by simp [ss,ht])
    · exact hQA.2
    · have hN : 2*1*2^ss.length=N := by simp [N,ss,Nat.pow_succ,Nat.mul_comm]
      rw [hN]
      simp only [Nat.one_mul] at hAcount; change N≤A+1 at hAcount
      dsimp [bA,M] at *
      omega
  let ds := strictFinish 1 (crossDirect bA v0.p ss)
  have hDrainC := strictDrain 1 (crossDirect bA v0.p ss) (by decide) hBudgetC
  have eLenC : (crossDirect bA v0.p ss).length=(v0::ss).length := by rw [←crossFarEq,crossLength]; rfl
  have eC : drain 0 0 (crossFar bA v0.p ss)=(ds,N-1,0) := by
    rw [crossFarEq]; simpa [ds,N,ss,eLenC] using hDrainC.2
  have gC : guarded 0 (crossFar bA v0.p ss) := by rw [crossFarEq]; exact hDrainC.1
  have lenC : ds.length=(v0::v1::v2::as).length := by rw [show ds=strictFinish 1 (crossDirect bA v0.p ss) from rfl,finishLength,eLenC]
  let a' := 1+2*(N-1)
  let b' := 1+2*A+1+(N-1)+0
  have ha' : a'=2*2^ds.length-1 := by rw [lenC]; change 1+2*(N-1)=2*N-1; omega
  have hb' : 3*2^ds.length-1≤b' := by rw [lenC]; change 3*N-1≤b'; simp only [Nat.one_mul] at hAcount; change N≤A+1 at hAcount; dsimp [b']; omega
  have step := zeroCycleSource a b x y z r v (d0::d1::d2::hs) ss ds v0 xs V A (N-1) rA 0
    (by have h : 0<M := Nat.pow_pos (by decide); change a=2*M-1 at ha; omega) (by omega) (by omega) hy hr hv hxs hcl
    (eCross.symm ▸ gA) (eCross.symm ▸ eA) validA gC eC
  have ex : v0.q=x := by dsimp [v0,u0]; omega
  rw [ex] at step
  exact ⟨a',b',ds,ha',hb',finishLower _ _ (by decide) hBudgetC,finishQBudget _ _ hBudgetC,by rw [lenC]; simp,reachesWeak (by omega) step⟩

/-- Reserve one or more units of the primary budget after the countdown.
    The tail width is preserved exactly. -/
theorem tertiaryEpochSlack (n slack a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool)
    (hp : primary (n+slack) a b cs) (hx : 3≤x) (hy : n+2≤y) (hc : counter xs=n) (hg : tailGood xs) :
    ∃ a' b' ds ys, primary slack a' b' ds ∧ clear ys ∧ tailGood ys ∧ ys.length=xs.length ∧
      reaches n (body a b x y cs xs U) (body a' b' (x+n) (y-n) ds ys U) := by
  induction n generalizing a b x y cs xs with
  | zero =>
    refine ⟨a,b,cs,xs,by simpa using hp,zeroClear xs hc,hg,rfl,?_⟩
    simp only [Nat.add_zero,Nat.sub_zero]; exact ⟨0,by decide,rfl⟩
  | succ n ih =>
    obtain ⟨lo,c,hi,he,hclear,hvalid,hf,hz,hg',hc'⟩ := tailDecrease xs hg (by omega)
    rw [he] at hc hc' ⊢
    rw [show n+1+slack=n+slack+1 by omega] at hp
    obtain ⟨a1,b1,cs1,hp1,hs⟩ := primaryCycle (n+slack) a b x y cs lo hi c U hp hx (by omega) hvalid hclear hf hz
    have hcount : counter (touch lo++target c::hi)=n := by omega
    obtain ⟨a2,b2,ds,ys,hp2,hcl,hg2,hlen,ht⟩ := ih a1 b1 (x+1) (y-1) cs1 (touch lo++target c::hi) hp1 (by omega) (by omega) hcount hg'
    refine ⟨a2,b2,ds,ys,hp2,hcl,hg2,by simpa [touch] using hlen,?_⟩
    have h := reachesTrans hs ht
    simpa only [show 1+n=n+1 by omega,show x+1+n=x+(n+1) by omega,show y-1-n=y-(n+1) by omega] using h

/-- All positive decrements and the representation-changing zero boundary.
    The new secondary marker consists of exactly one more set bit than the tertiary width. -/
theorem tertiaryToSecondary (n a b x y z r v : Nat) (cs : List PC) (xs : List TC) (V : List Bool)
    (hp : primary (n+1) a b cs) (hx : 3≤x) (hy : n+2≤y) (hr : 1≤r) (hc : counter xs=n) (hg : tailGood xs) :
    ∃ a' b' ds ys, a'=2*2^ds.length-1 ∧ 3*2^ds.length-1≤b' ∧ pLower 3 ds ∧ QBudget 1 1 ds ∧ 3≤ds.length ∧
      ys.length=xs.length ∧ tailGood ys ∧ clear ys ∧
      reaches (n+1) (body a b x y cs xs (zeroSuffix z r v V)) (secBody a' b' (x+n) (y-n) z r v ds ys V) := by
  obtain ⟨a1,b1,cs1,ys,hp1,hcl,hg1,hlen,hs⟩ := tertiaryEpochSlack n 1 a b x y cs xs (zeroSuffix z r v V) hp hx hy hc hg
  obtain ⟨a2,b2,ds,ha2,hb2,hp2,hq2,hm2,ht⟩ := primaryZero a1 b1 (x+n) (y-n) z r v cs1 ys V hp1 (by omega) (by omega) hr (tailValidOf ys hg1) hcl
  exact ⟨a2,b2,ds,ys,ha2,hb2,hp2,hq2,hm2,hlen,hg1,hcl,reachesTrans hs ht⟩

#print axioms primaryZero
#print axioms tertiaryEpochSlack
#print axioms tertiaryToSecondary
end BB6Coverage.Agent41F421.EpochWords
