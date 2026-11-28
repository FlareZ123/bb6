import F421AugmentedQGuard
import F421SecondaryFar

set_option linter.unusedSimpArgs false

namespace F421CreditLedger
open F421SecondaryLifetimes F421TertiaryGuard BB6Coverage.Agent41F421.EpochWords

/-- A tag stores normalized P lifetime and the cumulative Q birth credit
    through its original birth ID. The latter is immutable until deletion. -/
abbrev Tag := Nat × Nat

def tagAux (d : Nat) : List Tag → List Tag × Nat
  | [] => ([],d)
  | (l,q)::ts => if l=1 then tagAux (d+1) ts
    else let (ys,D) := tagAux d ts
         (((l-1)*2^d,q)::ys,D)

def creditDiff (prev : Nat) : List Tag → List Nat
  | [] => []
  | (_,q)::ts => (q-prev)::creditDiff q ts

def creditLast (prev : Nat) : List Tag → Nat
  | [] => prev
  | (_,q)::ts => creditLast q ts

def Ordered (prev : Nat) : List Tag → Prop
  | [] => True
  | (_,q)::ts => prev≤q ∧ Ordered q ts

def tagNext (ts : List Tag) : List Tag :=
  let (ys,D) := tagAux 0 ts
  ys++[(2^(D+1),creditLast 0 ts + (16*2^ts.length-1))]

theorem tagAuxP (d : Nat) (ts : List Tag) :
    ((tagAux d ts).1.map Prod.fst,(tagAux d ts).2)=advanceAux d (ts.map Prod.fst) := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨l,q⟩
    by_cases hl : l=1
    · simpa only [tagAux,List.map_cons,advanceAux,Prod.fst,ite_eq_left hl] using ih (d+1)
    · rcases he : tagAux d ts with ⟨ys,D⟩
      have H:=ih d
      rw [he] at H
      simp only [tagAux,List.map_cons,advanceAux,Prod.fst,Prod.snd,ite_eq_right hl,he,←H]

theorem tagNextP (ts : List Tag) : (tagNext ts).map Prod.fst=advance (ts.map Prod.fst) := by
  have H:=tagAuxP 0 ts
  rcases he : tagAux 0 ts with ⟨ys,D⟩
  rw [he] at H
  simp only [tagNext,he,List.map_append,List.map_singleton,advance,←H]

theorem orderedRaise (lo hi : Nat) (ts : List Tag) (hle : lo≤hi) (h : Ordered hi ts) : Ordered lo ts := by
  cases ts with
  | nil => trivial
  | cons t ts => exact ⟨Nat.le_trans hle h.1,h.2⟩

theorem lastRaise (lo hi : Nat) (ts : List Tag) (hle : lo≤hi) :
    creditLast lo ts≤creditLast hi ts := by
  cases ts with
  | nil => exact hle
  | cons t ts => exact Nat.le_refl _

theorem lastLower (p : Nat) (ts : List Tag) (h : Ordered p ts) : p≤creditLast p ts := by
  induction ts generalizing p with
  | nil => exact Nat.le_refl _
  | cons t ts ih => exact Nat.le_trans h.1 (ih t.2 h.2)

theorem tagAuxOrdered (p d : Nat) (ts : List Tag) (h : Ordered p ts) :
    Ordered p (tagAux d ts).1 ∧ creditLast p (tagAux d ts).1≤creditLast p ts := by
  induction ts generalizing p d with
  | nil => exact ⟨trivial,Nat.le_refl _⟩
  | cons t ts ih =>
    rcases t with ⟨l,q⟩
    by_cases hl : l=1
    · have H:=ih q (d+1) h.2
      simp only [tagAux,ite_eq_left hl]
      exact ⟨orderedRaise p q _ h.1 H.1,Nat.le_trans (lastRaise p q _ h.1) H.2⟩
    · have H:=ih q d h.2
      rcases he : tagAux d ts with ⟨ys,D⟩
      rw [he] at H
      simpa only [tagAux,ite_eq_right hl,he,Prod.fst,Ordered,creditLast] using And.intro (And.intro h.1 H.1) H.2

theorem creditDiffSnoc (p : Nat) (ts : List Tag) (t : Tag) :
    creditDiff p (ts++[t]) = creditDiff p ts ++ [t.2-creditLast p ts] := by
  induction ts generalizing p with
  | nil => rfl
  | cons u ts ih => simp only [List.cons_append,creditDiff,creditLast,ih]

theorem orderedSnoc (p : Nat) (ts : List Tag) (t : Tag)
    (h : Ordered p ts) (ht : creditLast p ts≤t.2) : Ordered p (ts++[t]) := by
  induction ts generalizing p with
  | nil => exact ⟨ht,trivial⟩
  | cons u ts ih => exact ⟨h.1,ih u.2 h.2 ht⟩

theorem tagNextOrdered (ts : List Tag) (h : Ordered 0 ts) : Ordered 0 (tagNext ts) := by
  have H:=tagAuxOrdered 0 0 ts h
  rcases he : tagAux 0 ts with ⟨ys,D⟩
  rw [he] at H
  simp only [tagNext,he]
  exact orderedSnoc 0 ys _ H.1 (by have := H.2; simp only [Prod.fst] at this; omega)

/-- Deleted credits telescope into the next surviving cumulative endpoint.
    The return carry is the gap from that endpoint to the last original tag. -/
theorem mergedTag (B d base prev : Nat) (ts : List Tag) (cs : List PC)
    (hB : 0<B) (hb : base≤prev) (ho : Ordered prev ts)
    (hp : pProjection cs=physicalP B (ts.map Prod.fst))
    (hq : augQ B cs=creditDiff prev ts) :
    mergedAug B (prev-base) cs =
      (creditDiff base (tagAux d ts).1, creditLast prev ts-creditLast base (tagAux d ts).1) := by
  induction ts generalizing B d base prev cs with
  | nil =>
    cases cs with
    | nil => rfl
    | cons c cs => simp [pProjection,physicalP] at hp
  | cons t ts ih =>
    rcases t with ⟨l,q⟩
    cases cs with
    | nil => simp [pProjection,physicalP] at hp
    | cons c cs =>
      simp only [pProjection,List.map_cons,physicalP,Prod.fst,List.cons.injEq] at hp
      simp only [augQ,creditDiff,List.cons.injEq] at hq
      have H := ho.1
      have Hq : c.q+B+(prev-base)=q-base := by omega
      have he : c.p=2*B ↔ l=1 := by
        rw [hp.1]
        have hb2 : 0<2*B := by omega
        constructor
        · intro h
          have h' : (2*B)*l=(2*B)*1 := by simpa using h
          exact Nat.eq_of_mul_eq_mul_left hb2 h'
        · intro h; simp [h]
      by_cases hl : l=1
      · have hd : c.p=2*B := he.mpr hl
        have hc : prev-base+c.q+B=q-base := by omega
        simp only [mergedAug,ite_eq_left hd,tagAux,ite_eq_left hl,creditLast,hc]
        exact ih (2*B) (d+1) base q cs (by omega) (by omega) ho.2 hp.2 hq.2
      · have hd : c.p≠2*B := fun h=>hl (he.mp h)
        have hi := ih (2*B) d q q cs (by omega) (Nat.le_refl _) ho.2 hp.2 hq.2
        rcases ht : tagAux d ts with ⟨ys,D⟩
        rw [ht,Nat.sub_self] at hi
        simp only [mergedAug,ite_eq_right hd,tagAux,ite_eq_right hl,ht,creditDiff,creditLast,Hq,Prod.fst,Prod.snd]
        rw [hi]

/-- Appending one birth after a deletion sweep preserves the exact credit
    vector by taking a difference of immutable cumulative endpoints. -/
theorem nextCredit (ts : List Tag) (h : Ordered 0 ts) :
    creditDiff 0 (tagNext ts) =
      creditDiff 0 (tagAux 0 ts).1 ++
        [16*2^ts.length-1 + (creditLast 0 ts-creditLast 0 (tagAux 0 ts).1)] := by
  have H := (tagAuxOrdered 0 0 ts h).2
  rcases he : tagAux 0 ts with ⟨ys,D⟩
  rw [he] at H
  simp only [Prod.fst] at H
  simp only [tagNext,he,creditDiffSnoc,Prod.snd,Prod.fst]
  have hh : creditLast 0 ts+(16*2^ts.length-1)-creditLast 0 ys =
      16*2^ts.length-1+(creditLast 0 ts-creditLast 0 ys) := by omega
  rw [hh]

#print axioms mergedTag
#print axioms nextCredit
end F421CreditLedger
