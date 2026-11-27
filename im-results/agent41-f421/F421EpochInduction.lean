import F421EpochGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421TertiaryGuard (drain QBudget Marked8 Survives8)

def primary (k a b : Nat) (cs : List PC) : Prop :=
  a=2*2^cs.length-1 ∧ b%8=7 ∧ pLower 3 cs ∧
    ∃ d0 d1 d2 hs, cs=d0::d1::d2::hs ∧
      3*k+3≤d0.q ∧ 6*k+4≤d1.q ∧ 12*k+6≤d2.q ∧ qMod hs

theorem pLowerCons (m : Nat) (c : PC) (cs : List PC) (hc : m≤c.p) (hs : pLower m cs) : pLower m (c::cs) := by
  intro z hz; rcases List.mem_cons.mp hz with rfl|hz
  · exact hc
  · exact hs z hz

theorem survivesLower (cs : List PC) (hs : Survives8 cs) : pLower 3 cs :=
  fun c hc => by have h := hs c hc; omega

theorem validOf (cs : List PC) (hp : pLower 3 cs) (k B : Nat) (hq : QBudget k B cs) : valid cs :=
  fun c hc => ⟨by have h := hp c hc; omega,qBudgetLower k B cs hq c hc⟩

theorem primaryCycle (k a b x y : Nat) (cs : List PC)
    (lo hi : List TC) (c : TC) (U : List Bool)
    (hg : primary (k+1) a b cs) (hx : 3≤x) (hy : 2≤y)
    (hlo : tailValid lo) (hclear : clear lo) (hc : c.f=true) (hz : 1≤c.z) :
    ∃ a' b' ds, primary k a' b' ds ∧ reaches 1 (body a b x y cs (lo++c::hi) U)
      (body a' b' (x+1) (y-1) ds (touch lo++target c::hi) U) := by
  rcases hg with ⟨ha,hb,hp,d0,d1,d2,hs,rfl,h0,h1,h2,hmod⟩
  have hp0 := hp d0 (by simp)
  have hp1 := hp d1 (by simp)
  have hp2 := hp d2 (by simp)
  have hph : pLower 3 hs := fun z hz => hp z (by simp [hz])
  have hv : valid (d0::d1::d2::hs) := by
    intro z hz
    have hz' := hp z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl|rfl|rfl|hz
    · exact ⟨by omega,by omega⟩
    · exact ⟨by omega,by omega⟩
    · exact ⟨by omega,by omega⟩
    · have hh := hmod z hz; exact ⟨by omega,by omega⟩
  let ah := crossDirect b d2.p hs
  let u0 : PC := ⟨d0.q,x-1⟩
  let u1 : PC := ⟨d1.q,d0.p-1⟩
  let u2 : PC := ⟨d2.q,d1.p-1⟩
  have eCross : crossFar b x (d0::d1::d2::hs)=u0::u1::u2::ah := by rw [crossFarEq]; rfl
  have hQa : QBudget 0 1 (u0::u1::u2::ah) := by
    rw [←eCross,crossFarEq]; exact crossQ b x 1 _ hx hp
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
  let w0 : PC := ⟨v0.p-1,v0.q⟩
  let w1 : PC := ⟨v1.p-1,v1.q⟩
  let w2 : PC := ⟨v2.p-1,v2.q⟩
  have eDec : dec (v0::v1::v2::as)=w0::w1::w2::dec as := rfl
  have hQb : QBudget 1 1 (w0::w1::w2::dec as) := eDec ▸ decQBudget 1 1 _ hQA
  have hmB : Marked8 (dec as) := F421TertiaryGuard.remark8 as hmAs
  have gB : guarded 0 (w0::w1::w2::dec as) := by
    apply guard3
    · dsimp [w0,v0,u0]; omega
    · dsimp [w1,v1,u1]; omega
    · dsimp [w2,v2,u2]; omega
    · exact qBudgetLower 1 1 _ hQb w0 (by simp)
    · exact qBudgetLower 1 1 _ hQb w1 (by simp)
    · exact qBudgetLower 1 1 _ hQb w2 (by simp)
    · exact markedGuard _ 7 8 1 hmB hQb.2.2.2
  rcases eBh : drain 7 0 (dec as) with ⟨bs,B,rB⟩
  let z0 : PC := ⟨w0.p-1,w0.q+1⟩
  let z1 : PC := ⟨w1.p-3,w1.q+2⟩
  let z2 : PC := ⟨w2.p-7,w2.q+4⟩
  have eB : drain 0 0 (w0::w1::w2::dec as)=(z0::z1::z2::bs,B,rB) := by
    rw [drain3 w0 w1 w2 (dec as) (by dsimp [w0,v0,u0]; omega) (by dsimp [w1,v1,u1]; omega) (by dsimp [w2,v2,u2]; omega),eBh]
  have modB := F421TertiaryGuard.drainMod8 (dec as) 7 0 (by decide) hmB
  rw [eBh] at modB
  obtain ⟨hmBs,hBm⟩ := modB
  have qB := F421TertiaryGuard.drainQ (w0::w1::w2::dec as) 1 1 1 0 0 (by decide) (by decide) hQb
  rw [eB] at qB
  obtain ⟨hQB,hLB,hBcount⟩ := qB
  have pB : pLower 3 (z0::z1::z2::bs) := by
    exact pLowerCons 3 z0 _ (by dsimp [z0,w0,v0,u0]; omega)
      (pLowerCons 3 z1 _ (by dsimp [z1,w1,v1,u1]; omega)
      (pLowerCons 3 z2 _ (by dsimp [z2,w2,v2,u2]; omega) (survivesLower bs hmBs)))
  have validB := validOf _ pB 2 1 hQB
  let N := 2^(z0::z1::z2::bs).length
  let M := 2^(d0::d1::d2::hs).length
  have lenA : (v0::v1::v2::as).length≤(d0::d1::d2::hs).length+1 := by
    rw [← eCross,crossLength] at hLA; exact hLA
  have lenB : (z0::z1::z2::bs).length≤(v0::v1::v2::as).length := by
    rw [←eDec] at hLB; simpa [dec] using hLB
  have hnM : N≤2*M := by
    have hh := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (Nat.le_trans lenB lenA)
    simpa [N,M,Nat.pow_succ,Nat.mul_comm] using hh
  have hn8 : N%8=0 := by
    dsimp [N]; simp only [List.length_cons,Nat.pow_succ]; omega
  have hnPos : 0<N := Nat.pow_pos (by decide)
  have hAm' : 3≤A := by omega
  have hBm' : 3≤B := by omega
  let bB := a+1+A+rA+1+B+rB
  let ss := z1::z2::bs
  have hBudgetC : strictBudget 1 (crossDirect bB z0.p ss) := by
    apply strictCross
    · exact pB z0 (by simp)
    · exact fun z hz => pB z (by simp [ss,hz])
    · exact hQB.2
    · have hN : 2*1*2^ss.length=N := by simp [N,ss,Nat.pow_succ,Nat.mul_comm]
      rw [hN]
      dsimp [bB,M] at *
      omega
  let ds := strictFinish 1 (crossDirect bB z0.p ss)
  have hDrainC := strictDrain 1 (crossDirect bB z0.p ss) (by decide) hBudgetC
  have eLenC : (crossDirect bB z0.p ss).length=(z0::ss).length := by
    rw [←crossFarEq,crossLength]; rfl
  have eC : drain 0 0 (crossFar bB z0.p ss)=(ds,N-1,0) := by
    rw [crossFarEq]
    simpa [ds,N,ss,eLenC] using hDrainC.2
  have gC : guarded 0 (crossFar bB z0.p ss) := by rw [crossFarEq]; exact hDrainC.1
  have pC : pLower 3 ds := finishLower _ _ (by decide) hBudgetC
  have lenC : ds.length=(z0::z1::z2::bs).length := by rw [show ds=strictFinish 1 (crossDirect bB z0.p ss) from rfl,finishLength,eLenC]
  let a' := 1+2*(N-1)
  let b' := 1+2*A+2+2*B+1+(N-1)+0
  have ha' : a'=2*2^ds.length-1 := by rw [lenC]; change 1+2*(N-1)=2*N-1; omega
  have hb' : b'%8=7 := by dsimp [b']; omega
  have hg' : primary k a' b' ds := by
    refine ⟨ha',hb',pC,?_⟩
    let e0 : PC := ⟨z1.q-1,z0.p-1+1⟩
    let e1 : PC := ⟨z2.q-3,z1.p-1+2⟩
    -- the third crossing uses either the first surviving head row or the leading ghost
    cases bs with
    | nil =>
      let e2 : PC := ⟨bB-7,z2.p-1+4⟩
      refine ⟨e0,e1,e2,[],rfl,?_,?_,?_,by simp [qMod]⟩
      · dsimp [e0,z0,w0,v0,u0]; omega
      · dsimp [e1,z1,w1,v1,u1]; omega
      · dsimp [e2,z2,w2,v2,u2]; omega
    | cons t ts =>
      let e2 : PC := ⟨t.q-7,z2.p-1+4⟩
      let rest := strictFinish 8 (crossDirect bB t.p ts)
      refine ⟨e0,e1,e2,rest,rfl,?_,?_,?_,?_⟩
      · dsimp [e0,z0,w0,v0,u0]; omega
      · dsimp [e1,z1,w1,v1,u1]; omega
      · dsimp [e2,z2,w2,v2,u2]; omega
      · have ht := hmBs t (by simp)
        exact finishMod bB t.p 8 ts ⟨ht.2,ht.1⟩ (by decide) (fun z hz => hmBs z (by simp [hz]))
  have step := cycleSource a b x y (d0::d1::d2::hs) (v0::v1::v2::as) ss ds z0 lo hi c U A B (N-1) rA rB 0
    (by have h : 0<M := Nat.pow_pos (by decide); change a=2*M-1 at ha; omega) (by omega) (by omega) hy hv hlo hclear hc hz
    (eCross.symm ▸ gA) (eCross.symm ▸ eA) validA (eDec.symm ▸ gB) (eDec.symm ▸ eB) validB gC eC
  have ez0 : z0.q=x+1 := by dsimp [z0,w0,v0,u0]; omega
  rw [ez0] at step
  exact ⟨a',b',ds,hg',reachesWeak (by omega) step⟩

#print axioms primaryCycle
end BB6Coverage.Agent41F421.EpochWords
