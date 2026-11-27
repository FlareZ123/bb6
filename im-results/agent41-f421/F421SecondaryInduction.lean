import F421SecondaryGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421TertiaryGuard (drain QBudget)

def crossTwice (B bA bB x : Nat) (cs : List PC) : List PC :=
  match strictFinish B (crossDirect bA x cs) with
  | [] => []
  | c::ds => strictFinish B (crossDirect bB c.p ds)

theorem crossTwiceEq (B bA bB x : Nat) (cs : List PC) (hB : 1≤B)
    (hp : pLower 1 cs) (hq : QBudget 2 B cs) (hb : 2*B*2^cs.length+2≤bA) :
    crossTwice B bA bB x cs=trimQ B cs++[⟨bB-(2*(B*2^cs.length)-1), bA-B*2^cs.length⟩] := by
  induction cs generalizing B x with
  | nil =>
    simp only [crossTwice,crossDirect,strictFinish,trimQ,List.nil_append,List.length_nil,Nat.pow_zero,Nat.mul_one]
    simp at hb
    congr 2 <;> omega
  | cons c cs ih =>
    have hp0 := hp c (by simp)
    have hq0 := hq.1
    have hp' : pLower 1 cs := fun z hz => hp z (by simp [hz])
    have hb' : 2*(2*B)*2^cs.length+2≤bA := by
      rw [show 2*(2*B)*2^cs.length=2*B*2^(cs.length+1) by rw [Nat.pow_succ]; ac_rfl]
      simpa using hb
    have hi := ih (2*B) c.p (by omega) hp' hq.2 hb'
    have hpow : (2*B)*2^cs.length=B*2^(c::cs).length := by simp only [List.length_cons,Nat.pow_succ]; ac_rfl
    rw [hpow] at hi
    -- the head of the second cross is the Q of the next B survivor
    cases cs with
    | nil =>
      simp [crossTwice,crossDirect,strictFinish,trimQ] at hi ⊢
      rw [show B*(2^1)=2*B by simp [Nat.mul_comm]]
      simp at hb
      congr 2 <;> omega
    | cons d ds =>
      simp only [crossTwice,crossDirect,strictFinish,trimQ,List.cons_append] at hi ⊢
      rw [←hi]
      congr 1
      · congr 1 <;> omega

theorem sPAppend (k B : Nat) (cs ds : List PC) (hc : sPGood k B cs)
    (hd : sPGood k (B*2^cs.length) ds) : sPGood k B (cs++ds) := by
  induction cs generalizing B with
  | nil => simpa using hd
  | cons c cs ih =>
    refine ⟨hc.1,ih _ hc.2 ?_⟩
    have he : 2*B*2^cs.length=B*2^(c::cs).length := by simp only [List.length_cons,Nat.pow_succ]; ac_rfl
    rw [he]; exact hd

theorem sQAppend (k B : Nat) (cs ds : List PC) (hc : QBudget k B cs)
    (hd : QBudget k (B*2^cs.length) ds) : QBudget k B (cs++ds) := by
  induction cs generalizing B with
  | nil => simpa using hd
  | cons c cs ih =>
    refine ⟨hc.1,ih _ hc.2 ?_⟩
    have he : 2*B*2^cs.length=B*2^(c::cs).length := by simp only [List.length_cons,Nat.pow_succ]; ac_rfl
    rw [he]; exact hd

theorem qBudgetDouble (B : Nat) (cs : List PC) (hq : QBudget 2 B cs) : QBudget 1 (2*B) cs := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih => exact ⟨by have h := hq.1; omega,by simpa [Nat.mul_assoc] using ih (2*B) hq.2⟩

/-- The deterministic primary arithmetic of a positive secondary cycle. -/
def sNext (b : Nat) (cs : List PC) : Nat × Nat × List PC :=
  let (as,A,rA) := drain 0 0 (dec cs)
  let D := 2^as.length
  (4*D-1,6*D-1,trimQ 1 as++[⟨4*2^cs.length,b+1+A+rA-D⟩])

/-- A positive secondary cycle returns the same mixed guard with one less unit.
    Leading b need only have the lower bound 3M-1, not the equality. -/
theorem secondaryPrimaryCycleExact (k a b x y : Nat) (cs : List PC) (lo hi : List TC) (c : TC) (U : List Bool)
    (hg : sPrimary (k+1) a b cs) (hx : 4≤x) (hy : 3≤y)
    (hxs : stailGood (lo++c::hi)) (hlo : clear lo) (hc : c.f=true) :
    let (a',b',ds) := sNext b cs
    sPrimary k a' b' ds ∧ reaches 1 (sbody a b x y cs (lo++c::hi) U)
      (sbody a' b' (x-1) (y-1) ds (sTouch lo++sTarget c::hi) U) := by
  rcases hg with ⟨ha,hb,hp,hq,hlen⟩
  let M := 2^cs.length
  have hM : 2≤M := Nat.pow_le_pow_right (n:=2) (by decide) hlen
  have hpp := sPgoodLower (k+1) 1 cs (by decide) hp
  have hv := validOf _ hpp 1 1 hq
  have hA := sDrainA k 1 1 0 cs (by decide) (by decide) (by decide) (by decide) (by simp) hp hq
  rcases eA : drain 0 0 (dec cs) with ⟨as,A,rA⟩
  simp only [Nat.sub_self,Nat.one_mul,eA] at hA
  rcases hA with ⟨gA,hAc,hpA,hqA,hlenA⟩
  let D := 2^as.length
  have hDM : D≤M := Nat.pow_le_pow_right (n:=2) (by decide) hlenA
  have hDpos : 0<D := Nat.pow_pos (by decide)
  have hAlen : 1≤as.length := by
    cases cs with
    | nil => simp at hlen
    | cons e es =>
      have hfirst := sPgoodStep k 1 e (by decide) hp.1
      have hprot : 2*1*(k+1)+3≤e.p := hp.1.resolve_right (by omega)
      have hd : ¬e.p-1≤2*0+1 := by omega
      change drain 0 0 (⟨e.p-1,e.q⟩::dec es)=(as,A,rA) at eA
      simp only [drain,ite_eq_right hd] at eA
      rcases he : drain (2*0+1) 0 (dec es) with ⟨ds,H,r⟩
      rw [he] at eA
      cases eA; simp
  have hD : 2≤D := Nat.pow_le_pow_right (n:=2) (by decide) hAlen
  have hpAlow := sPgoodLower k 1 as (by decide) hpA
  have vA := validOf _ hpAlow 2 1 hqA
  let aA := a+2+2*A
  let bA := b+1+A+rA
  let inputB := crossDirect bA (x-1) as
  have hcrossB : crossFar bA (x-1) as=inputB := crossFarEq _ _ _
  have hbudgetB : strictBudget 1 inputB := by
    dsimp [inputB]
    apply strictCrossOne
    · omega
    · exact hpAlow
    · exact qBudgetDouble 1 as hqA
    · change 2*D+2≤bA
      dsimp [bA,M] at *; omega
  have hDrainB := strictDrain 1 inputB (by decide) hbudgetB
  let outputB := strictFinish 1 inputB
  have eLenB : outputB.length=as.length+1 := by
    rw [show outputB=strictFinish 1 inputB from rfl,finishLength,show inputB=crossFar bA (x-1) as from hcrossB.symm,crossLength]
  let N := 2*D
  have hN : 2^inputB.length=N := by
    rw [←hcrossB,crossLength,Nat.pow_succ]; simp [N,D,Nat.mul_comm]
  have eB : drain 0 0 (crossFar bA (x-1) as)=(outputB,N-1,0) := by
    rw [hcrossB]; simpa [outputB,hN] using hDrainB.2
  have gB : guarded 0 (crossFar bA (x-1) as) := by rw [hcrossB]; exact hDrainB.1
  have pB : pLower 3 outputB := finishLower 1 inputB (by decide) hbudgetB
  have qB : QBudget 1 1 outputB := finishQBudget 1 inputB hbudgetB
  have vB := validOf outputB pB 1 1 qB
  cases he : outputB with
  | nil => simp [he] at eLenB
  | cons cB bs =>
    have hqB : cB.q=x-1 := by
      cases as with
      | nil => simp at hAlen
      | cons t ts =>
        simp only [outputB,inputB,crossDirect,strictFinish,List.cons.injEq] at he
        have h := congrArg F421TertiaryGuard.Cell.q he.1
        simp at h; omega
    let bB := aA+1+(N-1)
    let inputC := crossDirect bB cB.p bs
    have hcrossC : crossFar bB cB.p bs=inputC := crossFarEq _ _ _
    have hlenC : inputC.length=as.length+1 := by
      rw [←hcrossC,crossLength]; simp only [he,List.length_cons] at eLenB; omega
    have hNC : 2^inputC.length=N := by rw [hlenC,Nat.pow_succ]; simp [N,D,Nat.mul_comm]
    have hbudgetC : strictBudget 1 inputC := by
      dsimp [inputC]; apply strictCrossOne
      · exact pB cB (by rw [he]; simp)
      · exact fun t ht => pB t (by rw [he]; simp [ht])
      · rw [he] at qB; exact qB.2
      · have hh : 2*1*2^bs.length=N := by
          have hlen' : bs.length=as.length := by rw [he] at eLenB; simp at eLenB; exact eLenB
          simp [hlen',N,D]
        rw [hh]
        dsimp [bB,aA,M] at *; omega
    let ds := strictFinish 1 inputC
    have hDrainC := strictDrain 1 inputC (by decide) hbudgetC
    have eC : drain 0 0 (crossFar bB cB.p bs)=(ds,N-1,0) := by rw [hcrossC]; simpa [ds,hNC] using hDrainC.2
    have gC : guarded 0 (crossFar bB cB.p bs) := by rw [hcrossC]; exact hDrainC.1
    have lenDs : ds.length=as.length+1 := by rw [show ds=strictFinish 1 inputC from rfl,finishLength,hlenC]
    have hDs : ds=trimQ 1 as++[⟨4*M,bA-D⟩] := by
      have h := crossTwiceEq 1 bA bB (x-1) as (by decide) (fun t ht => by have hh := hpAlow t ht; omega) hqA (by dsimp [bA,M,D]; omega)
      change (match outputB with | [] => [] | c::ds => strictFinish 1 (crossDirect bB c.p ds))=_ at h
      rw [he] at h
      change ds=_ at h
      rw [h]
      simp only [Nat.one_mul]
      have hh : bB-(2*D-1)=4*M := by dsimp [bB,aA,N]; change a=2*M-1 at ha; change A=M-1 at hAc; omega
      rw [show 2*2^as.length=2*D from rfl,hh]
    let a' := 1+2*(N-1)
    let b' := 1+2*(N-1)+1+(N-1)+0
    have ha' : a'=2*2^ds.length-1 := by rw [lenDs,Nat.pow_succ]; dsimp [a',N,D]; omega
    have hb' : 3*2^ds.length-1≤b' := by rw [lenDs,Nat.pow_succ]; dsimp [b',N,D]; omega
    have hnew : sPGood k D [⟨4*M,bA-D⟩] := by
      have hdvd : D∣M := Nat.pow_dvd_pow 2 hlenA
      obtain ⟨t,ht⟩ := hdvd
      have htpos : 0<t := by by_cases h : t=0; simp [h] at ht; omega; omega
      refine ⟨Or.inr ⟨hD,⟨2*t,by omega,?_⟩⟩,trivial⟩
      rw [ht]; ac_rfl
    have hqnew : QBudget 1 D [⟨4*M,bA-D⟩] := by
      refine ⟨?_,trivial⟩
      change 2+1*D≤bA-D
      dsimp [bA,M] at *; omega
    have hp' : sPGood k 1 ds := by rw [hDs]; apply sPAppend _ _ _ _ (trimPGood _ _ _ hpA); simpa [trimLength,D] using hnew
    have hq' : QBudget 1 1 ds := by rw [hDs]; apply sQAppend _ _ _ _ (trimQGood _ _ hqA); simpa [trimLength,D] using hqnew
    have htail := stailValid _ hxs
    have hxs' : svalid (lo++c::hi) := fun t ht => by have h := htail t ht; omega
    have hzh : ∀ t∈lo, 2≤t.z := fun t ht => (htail t (by simp [ht])).1
    have hcc := htail c (by simp)
    have hhi : svalid hi := fun t ht => by have h := htail t (by simp [ht]); omega
    have step := secondaryCycleSource a b x y cs as bs ds cB lo hi c U A (N-1) (N-1) rA 0 0
      (by change 3*M-1≤b at hb; omega) (by omega) (by omega) hv hxs' hlo hzh hc (by omega) (by omega) hhi
      gA eA vA gB (he ▸ eB) (he ▸ vB) gC eC
    rw [hqB] at step
    have hh : sNext b cs = (a',b',ds) := by
      unfold sNext
      rw [eA]
      change (4*D-1,6*D-1,trimQ 1 as++[⟨4*M,b+1+A+rA-D⟩]) = _
      rw [hDs]
      change (4*D-1,6*D-1,trimQ 1 as++[⟨4*M,bA-D⟩]) = (a',b',trimQ 1 as++[⟨4*M,bA-D⟩])
      dsimp [a',b',N]
      congr 2 <;> omega
    rw [hh]
    exact ⟨⟨ha',hb',hp',hq',by rw [lenDs]; omega⟩,reachesWeak (by omega) step⟩

theorem secondaryPrimaryCycle (k a b x y : Nat) (cs : List PC) (lo hi : List TC) (c : TC) (U : List Bool)
    (hg : sPrimary (k+1) a b cs) (hx : 4≤x) (hy : 3≤y)
    (hxs : stailGood (lo++c::hi)) (hlo : clear lo) (hc : c.f=true) :
    ∃ a' b' ds, sPrimary k a' b' ds ∧ reaches 1 (sbody a b x y cs (lo++c::hi) U)
      (sbody a' b' (x-1) (y-1) ds (sTouch lo++sTarget c::hi) U) := by
  have h := secondaryPrimaryCycleExact k a b x y cs lo hi c U hg hx hy hxs hlo hc
  rcases he : sNext b cs with ⟨a',b',ds⟩
  rw [he] at h
  exact ⟨a',b',ds,h⟩

#print axioms crossTwiceEq
#print axioms secondaryPrimaryCycleExact
#print axioms secondaryPrimaryCycle
end BB6Coverage.Agent41F421.EpochWords
