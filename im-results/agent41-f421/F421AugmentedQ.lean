import F421SecondaryQGrowth

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

/-- Positional Q credits. These are the values that merge without arithmetic
    when a marked P cell is deleted. -/
def augQ (B : Nat) : List PC → List Nat
  | [] => []
  | c::cs => (c.q+B)::augQ (2*B) cs

def mergedAug (B carry : Nat) : List PC → List Nat × Nat
  | [] => ([],carry)
  | c::cs =>
    if c.p=2*B then mergedAug (2*B) (carry+c.q+B) cs
    else let (ys,r):=mergedAug (2*B) 0 cs
         ((c.q+B+carry)::ys,r)

/-- Exact far-to-near merged Q credit vector from the actual marked drain,
    with all terminal deleted cells folded into their nearest survivor. -/
theorem drainAug (B carry : Nat) (cs : List PC)
    (hB : 0<B) (hp : capP B (pProjection cs)) :
    ((drain (B-1) carry (dec cs)).1.map Cell.q,
      (drain (B-1) carry (dec cs)).2.2) = mergedAug B carry cs := by
  induction cs generalizing B carry with
  | nil => simp [drain,dec,mergedAug]
  | cons c cs ih =>
    have htail : capP (2*B) (pProjection cs) := hp.2
    have hB' : 0<2*B := by omega
    have hc : 2*(B-1)+1=2*B-1 := by omega
    rcases hp.1 with h|h
    · have hle : c.p-1≤2*(B-1)+1 := by omega
      have ht : (c.p-1+1)/2=B := by omega
      have hle' : c.p-1≤2*B-1 := by omega
      have hi := ih (2*B) (carry+c.q+B) hB' htail
      simp only [dec,List.map_cons,drain,hc,if_pos hle',ht,show B-1+B=2*B-1 by omega]
      simp only [mergedAug,if_pos h]
      simpa only [dec] using hi
    · have hn : ¬c.p-1≤2*(B-1)+1 := by omega
      have hn' : ¬c.p-1≤2*B-1 := by omega
      have hi := ih (2*B) 0 hB' htail
      rcases he : drain (2*B-1) 0 (dec cs) with ⟨ys,H,r⟩
      rw [he] at hi
      have he' : drain (2*B-1) 0 (List.map (fun c : PC => ⟨c.p-1,c.q⟩) cs)=(ys,H,r) := by
        simpa [dec] using he
      simp only [dec,List.map_cons,drain,hc,if_neg hn',he',
        List.map_cons,Cell.q,Prod.fst,Prod.snd]
      have hne : c.p ≠ 2*B := by omega
      simp only [mergedAug,if_neg hne]
      change ((c.q+(B-1)+1+carry)::ys.map Cell.q,r) =
        ((c.q+B+carry)::(mergedAug (2*B) 0 cs).1,(mergedAug (2*B) 0 cs).2)
      rw [←hi]
      simp only [Prod.fst,Prod.snd]
      have heq : c.q+(B-1)+1+carry=c.q+B+carry := by omega
      rw [heq]

theorem augQAppend (B : Nat) (xs ys : List PC) :
    augQ B (xs++ys)= augQ B xs ++augQ (B*2^xs.length) ys := by
  induction xs generalizing B with
  | nil => simp [augQ]
  | cons c xs ih =>
    simp only [List.cons_append,augQ,List.length_cons,List.cons.injEq,eq_self_iff_true,true_and]
    rw [ih]
    congr 1
    rw [Nat.pow_succ]
    ac_rfl

theorem trimQLength (B : Nat) (cs : List PC) :
    (trimQ B cs).length=cs.length := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih => simp [trimQ,ih]

theorem augTrim (B : Nat) (cs : List PC) (hq : qAtLeast B cs) :
    augQ B (trimQ B cs) = cs.map Cell.q := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih =>
    have hq0 : B≤c.q := hq.1
    simp only [trimQ,augQ,List.map_cons,Cell.q]
    rw [ih (2*B) hq.2]
    congr 1
    omega

/-- Exact original-source vector Q recurrence as grouping-plus-append,
    independent of all enormous Q-run arithmetic and deletion patterns. -/
theorem sNextAug (b : Nat) (cs : List PC)
    (hp : capP 1 (pProjection cs))
    (hq : qAtLeast 1 (drain 0 0 (dec cs)).1)
    (hb : 2^cs.length ≤ b+1) :
    augQ 1 ((sNext b cs).2.2) =
      (mergedAug 1 0 cs).1 ++ [b+2^cs.length+(mergedAug 1 0 cs).2] := by
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  rw [he] at hq
  have hd := drainAug 1 0 cs (by decide) hp
  rw [he] at hd
  simp only [Prod.fst,Prod.snd] at hd
  have ht := drainHorizon 1 0 cs (by decide) hp
  rw [he] at ht
  simp only [Nat.one_mul,Prod.fst,Prod.snd] at ht
  have hlen := drainLengthLe 0 0 (dec cs)
  rw [he] at hlen
  simp only [Prod.fst,Prod.snd] at hlen
  have hlen' : as.length≤cs.length := by simpa [dec] using hlen
  have hpow : 2^as.length≤2^cs.length := Nat.pow_le_pow_right (n:=2) (by decide) hlen'
  have hadd : 2^as.length≤b+1+A+r := by omega
  unfold sNext
  rw [he]
  simp only [Prod.fst,Prod.snd,augQAppend,List.length_append]
  have htrim := augTrim 1 as hq
  rw [htrim]
  simp only [augQ,List.length_singleton,Nat.one_mul,List.map_singleton,Cell.q]
  rw [trimQLength 1 as]
  change as.map Cell.q ++ [b+1+A+r-2^as.length+2^as.length] = _
  have hM : 0<2^cs.length := Nat.pow_pos (by decide)
  have hcancel : b+1+A+r-2^as.length+2^as.length=b+2^cs.length+r := by omega
  rw [hcancel]
  rcases hm : mergedAug 1 0 cs with ⟨ys,carry⟩
  rw [hm] at hd
  have hleft : as.map Cell.q=ys := congrArg Prod.fst hd
  have hright : r=carry := congrArg Prod.snd hd
  rw [hleft,hright]

#print axioms drainAug
#print axioms sNextAug
end F421SecondaryLifetimes
