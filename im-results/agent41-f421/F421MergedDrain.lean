import F421GeneralDrain
import TertiaryGuard

namespace BB6Coverage.Agent41F421.MergedDrain
open Agent31Pump Regular F421DrainPlan
open F421TertiaryGuard (Cell drain)
open GeneralDrain (farWord rowWord)

def toRow (m : Bool) (c : Cell) : Row := ⟨c.p,c.q,m⟩
def rows (m : Bool) (cs : List Cell) : List Row := cs.map (toRow m)
def word (m : Bool) (cs : List Cell) : List Bool := farWord (rows m cs)

def guarded (h : Nat) : List Cell → Prop
  | [] => True
  | c::cs => 2≤c.q ∧ 1≤c.p ∧ (c.p ≤ 2*h+1 → c.p%2=1) ∧
      guarded (h + (min c.p (2*h+1)+1)/2) cs

theorem planGuard (cs : List Cell) (h : Nat) (hg : guarded h cs) : good h (rows true cs) := by
  induction cs generalizing h with
  | nil => trivial
  | cons c cs ih =>
    rcases hg with ⟨hq,hp,he,ht⟩
    exact ⟨⟨hq,fun _ => hp,he⟩,ih _ ht⟩

theorem allOddGuard (cs : List Cell) (h : Nat) (hg : ∀ c∈cs, 2≤c.q ∧ c.p%2=1) : guarded h cs := by
  induction cs generalizing h with
  | nil => trivial
  | cons c cs ih =>
    obtain ⟨hq,hp⟩ := hg c (by simp)
    exact ⟨hq,by omega,fun _ => hp,ih _ (fun x hx => hg x (by simp [hx]))⟩

/-- The normalized calculation gives the same terminal count and tape word
    as the exact arbitrary-marker plan. The trailing carry merges into
    the next surviving Q run, or into the leading Q at the near end. -/
theorem drainWord (cs : List Cell) (h carry : Nat) :
    let (ys,H,r) := drain h carry cs
    count h (rows true cs) = H ∧
      farWord (finish h (rows true cs)) ++ rep Q carry = rep Q r ++ word false ys := by
  induction cs generalizing h carry with
  | nil => simp [drain,count,rows,finish,farWord,GeneralDrain.nearWord,word]
  | cons c cs ih =>
    by_cases hd : c.p≤2*h+1
    · let t := (c.p+1)/2
      have hn : nextH h (toRow true c)=h+t := by simp [nextH,terminals,visits,bit,toRow,Nat.min_eq_left hd,t]
      have hf : finishRow h (toRow true c)=⟨0,c.q+t,false⟩ := by simp [finishRow,terminals,visits,bit,toRow,Nat.min_eq_left hd,t]
      rcases he : drain (h+t) (carry+c.q+t) cs with ⟨ys,H,r⟩
      have hi := ih (h+t) (carry+c.q+t)
      rw [he] at hi
      simp only [drain,if_pos hd, ← show t=(c.p+1)/2 from rfl,he]
      change count (nextH h (toRow true c)) (rows true cs)=H ∧
        farWord (finishRow h (toRow true c)::finish (nextH h (toRow true c)) (rows true cs)) ++ rep Q carry = rep Q r ++ word false ys
      rw [hn,hf,GeneralDrain.farCons]
      refine ⟨hi.1,?_⟩
      simp only [rowWord,rep, Bool.false_eq_true, if_false,List.nil_append]
      rw [List.append_assoc, ← repAdd, show c.q+t+carry=carry+c.q+t by omega]
      exact hi.2
    · have hn : nextH h (toRow true c)=2*h+1 := by simp [nextH,terminals,visits,bit,toRow,Nat.min_eq_right (by omega : 2*h+1≤c.p)]; omega
      have hf : finishRow h (toRow true c)=⟨c.p-(2*h+1),c.q+h+1,false⟩ := by simp [finishRow,terminals,visits,bit,toRow,Nat.min_eq_right (by omega : 2*h+1≤c.p)]; omega
      rcases he : drain (2*h+1) 0 cs with ⟨ys,H,r⟩
      have hi := ih (2*h+1) 0
      rw [he] at hi
      simp only [drain,if_neg hd,he]
      change count (nextH h (toRow true c)) (rows true cs)=H ∧
        farWord (finishRow h (toRow true c)::finish (nextH h (toRow true c)) (rows true cs)) ++ rep Q carry = rep Q r ++ word false (⟨c.p-(2*h+1),c.q+h+1+carry⟩::ys)
      rw [hn,hf,GeneralDrain.farCons]
      refine ⟨hi.1,?_⟩
      have hi' : farWord (finish (2*h+1) (rows true cs)) = rep Q r ++ word false ys := by simpa [rep] using hi.2
      rw [hi']
      simp only [word,rows,List.map_cons,GeneralDrain.farCons,rowWord,toRow,Bool.false_eq_true,if_false,List.append_nil]
      simp only [repAdd,List.append_assoc]

theorem mergedDrain (cs : List Cell) (a b : Nat) (U : List Bool)
    (hb : 2≤b) (hg : guarded 0 cs) :
    let (ys,H,r) := drain 0 0 cs
    ∃ n, H≤n ∧ run0 table n (frontier (rep P a++rep Q b++word true cs++U)) =
      some (frontier (rep P (a+2*H)++rep Q (b+H+r)++word false ys++U)) := by
  rcases he : drain 0 0 cs with ⟨ys,H,r⟩
  have hw := drainWord cs 0 0
  rw [he] at hw
  have he' : farWord (finish 0 (rows true cs))=rep Q r++word false ys := by simpa [rep] using hw.2
  obtain ⟨n,hn,hr⟩ := GeneralDrain.generalDrain (rows true cs) a b U hb (planGuard cs 0 hg)
  rw [hw.1,he'] at hr
  refine ⟨n,hw.1 ▸ hn,?_⟩
  simpa only [word,repAdd,List.append_assoc] using hr

#print axioms drainWord
#print axioms mergedDrain
end BB6Coverage.Agent41F421.MergedDrain
