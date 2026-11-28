import F421CreditLedger

set_option linter.unusedSimpArgs false

namespace F421CreditLedger
open F421SecondaryLifetimes F421TertiaryGuard BB6Coverage.Agent41F421.EpochWords

/-- Equality of the two leading coordinates after any successor, directly
    from sNext and the survivor count. -/
theorem headExact (b : Nat) (cs : List PC) :
    (sNext b cs).1=2*2^(sNext b cs).2.2.length-1 ∧
    (sNext b cs).2.1=3*2^(sNext b cs).2.2.length-1 := by
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  simp only [sNext,he,Prod.fst,Prod.snd,List.length_append,trimQLength,List.length_singleton,Nat.pow_succ]
  constructor <;> omega

/-- A single normalized P/Q step with the two protected far cells. -/
theorem nextSource (k a b p0 q0 p1 q1 : Nat) (cs : List PC) (ts : List Tag)
    (h0 : 3≤p0) (h1 : 5≤p1)
    (hg : sPrimary (k+1) a b (⟨p0,q0⟩::⟨p1,q1⟩::cs))
    (hb : b=3*2^(cs.length+2)-1)
    (hpos : Positive (ts.map Prod.fst)) (ho : Ordered 0 ts)
    (hp : pProjection cs=physicalP 4 (ts.map Prod.fst))
    (hq : augQ 4 cs=creditDiff 0 ts) :
    ∃ a' b' ds,
      sNext b (⟨p0,q0⟩::⟨p1,q1⟩::cs)=(a',b',⟨p0-2,q0⟩::⟨p1-4,q1⟩::ds) ∧
      pProjection ds=physicalP 4 ((tagNext ts).map Prod.fst) ∧
      augQ 4 ds=creditDiff 0 (tagNext ts) ∧
      a'=2*2^(ds.length+2)-1 ∧ b'=3*2^(ds.length+2)-1 := by
  obtain ⟨a',b',ds,he,hp'⟩ := nextShapeFar b p0 q0 p1 q1 cs _ h0 h1 hpos hp
  have hhead := headExact b (⟨p0,q0⟩::⟨p1,q1⟩::cs)
  rw [he] at hhead
  simp only [Prod.fst,Prod.snd,List.length_cons] at hhead
  have hqa := sNextAugGuarded k a b (⟨p0,q0⟩::⟨p1,q1⟩::cs) hg
  rw [he] at hqa
  have hm := mergedTag 4 0 0 0 ts cs (by decide) (by decide) ho hp hq
  simp only [Nat.sub_self] at hm
  have h0' : p0≠2*1 := by omega
  have h1' : p1≠2*(2*1) := by omega
  have hlen : cs.length=ts.length := by
    have h := congrArg List.length hp
    simpa only [pProjection,List.length_map,physicalPLength] using h
  have hweight : b+2^(cs.length+2)=16*2^ts.length-1 := by
    rw [hb,hlen,Nat.pow_add]
    have hpos : 0<2^ts.length := Nat.pow_pos (by decide)
    omega
  simp only [Prod.snd,augQ,mergedAug,ite_eq_right h0',ite_eq_right h1',
    show 2*(2*1)=4 by decide,show 2*1=2 by decide,Nat.zero_add,Nat.add_zero,hm,Prod.fst,
    List.cons_append,List.cons.injEq,List.length_cons] at hqa
  have H := hqa.2.2
  rw [show cs.length+1+1=cs.length+2 by omega,hweight] at H
  rw [←nextCredit ts ho] at H
  refine ⟨a',b',ds,he,?_,H,?_,?_⟩
  · simpa only [tagNextP] using hp'
  · simpa only [show ds.length+1+1=ds.length+2 by omega] using hhead.1
  · simpa only [show ds.length+1+1=ds.length+2 by omega] using hhead.2

/-- Guard transport uses the already proved source cycle, specialized to a
    dummy one-cell tail. The primary successor is tail independent. -/
theorem primaryStep (k a b : Nat) (cs : List PC) (h : sPrimary (k+1) a b cs) :
    sPrimary k (sNext b cs).1 (sNext b cs).2.1 (sNext b cs).2.2 := by
  exact (secondaryPrimaryCycleExact k a b 4 3 cs [] [] ⟨2,2,true⟩ [] h
    (by decide) (by decide) (by simp [stailGood,counter]) (by simp [clear]) rfl).1

def tagIter : Nat → List Tag → List Tag
  | 0,ts => ts
  | k+1,ts => tagIter k (tagNext ts)

/-- Full paired coordinate recurrence for any guarded secondary epoch. -/
theorem iterateSource (k a b p0 q0 p1 q1 : Nat) (cs : List PC) (ts : List Tag)
    (h0 : 2*k+3≤p0) (h1 : 4*k+5≤p1)
    (hg : sPrimary k a b (⟨p0,q0⟩::⟨p1,q1⟩::cs))
    (ha : a=2*2^(cs.length+2)-1) (hb : b=3*2^(cs.length+2)-1)
    (hpos : Positive (ts.map Prod.fst)) (ho : Ordered 0 ts)
    (hp : pProjection cs=physicalP 4 (ts.map Prod.fst))
    (hq : augQ 4 cs=creditDiff 0 ts) :
    ∃ a' b' ds,
      sIter k (a,b,⟨p0,q0⟩::⟨p1,q1⟩::cs)=(a',b',⟨p0-2*k,q0⟩::⟨p1-4*k,q1⟩::ds) ∧
      pProjection ds=physicalP 4 ((tagIter k ts).map Prod.fst) ∧
      augQ 4 ds=creditDiff 0 (tagIter k ts) ∧
      a'=2*2^(ds.length+2)-1 ∧ b'=3*2^(ds.length+2)-1 := by
  induction k generalizing a b p0 q0 p1 q1 cs ts with
  | zero => exact ⟨a,b,cs,by simp [sIter],hp,hq,ha,hb⟩
  | succ k ih =>
    obtain ⟨a1,b1,ds,he,hp1,hq1,ha1,hb1⟩ := nextSource k a b p0 q0 p1 q1 cs ts
      (by omega) (by omega) hg hb hpos ho hp hq
    have hg1 := primaryStep k a b (⟨p0,q0⟩::⟨p1,q1⟩::cs) hg
    rw [he] at hg1
    have hpos1 : Positive ((tagNext ts).map Prod.fst) := by
      rw [tagNextP]
      exact advancePositive _ hpos
    obtain ⟨a2,b2,es,he2,hp2,hq2,ha2,hb2⟩ := ih a1 b1 (p0-2) q0 (p1-4) q1 ds
      (tagNext ts) (by omega) (by omega) hg1 ha1 hb1 hpos1 (tagNextOrdered ts ho) hp1 hq1
    refine ⟨a2,b2,es,?_,hp2,hq2,ha2,hb2⟩
    simp only [sIter,he,he2]
    rw [show p0-2-2*k=p0-2*(k+1) by omega,show p1-4-4*k=p1-4*(k+1) by omega]

def firstTags : List Tag := [(327661,3145739),(14,6294521),(30,6297591),(6,6300661),
  (22,6304756),(14,6308851),(1,6309874),(2,6311921)]

theorem firstCreditEndpoint :
    ∃ a b ds,
      sIter 32750 (2047,3071,firstPrimary)=(a,b,⟨2818045,131073⟩::⟨6946811,2883586⟩::ds) ∧
      pProjection ds=physicalP 4 ((tagIter 32750 firstTags).map Prod.fst) ∧
      augQ 4 ds=creditDiff 0 (tagIter 32750 firstTags) ∧
      a=2*2^(ds.length+2)-1 ∧ b=3*2^(ds.length+2)-1 := by
  have h:=iterateSource 32750 2047 3071 2883545 131073 7077811 2883586 firstHead firstTags
    (by decide) (by decide) firstPrimaryGood (by decide) (by decide)
    (by simp [Positive,firstTags]) (by simp [Ordered,firstTags]) (by decide) (by decide)
  simpa only [show firstPrimary=⟨2883545,131073⟩::⟨7077811,2883586⟩::firstHead from rfl,
    show 2883545-2*32750=2818045 by decide,show 7077811-4*32750=6946811 by decide] using h

#print axioms firstCreditEndpoint
#print axioms nextSource
end F421CreditLedger
