import F421Frontier

namespace BB6Coverage.Agent41F421
open BB6Coverage Agent31Pump

namespace Regular

def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def Z : List Bool := [false,false]
def R : List Bool := [true,true]

/-- Parameters (q,p) represent actual run lengths q+2 and p+1. -/
abbrev Seg := Nat × Nat

def segBlocks (s : Seg) : List Block :=
  .c :: (List.replicate s.1 .a ++ [.b] ++ List.replicate s.2 .a)
def segPairs (s : Seg) : List Pair :=
  .o1 :: (List.replicate (s.1+2) .o0 ++ List.replicate s.2 .z1)
def segInput (s : Seg) : List Bool := rep Q (s.1+2) ++ rep P (s.2+1)
def segOutput (s : Seg) : List Bool := Z ++ rep Q (s.1+2) ++ rep P s.2

def segCost (s : Seg) : Nat := 8*(s.1+2)+4*(s.2+1)

def blocks (ss : List Seg) : List Block := ss.flatMap segBlocks
def pairs (ss : List Seg) : List Pair := ss.flatMap segPairs
def inputs (ss : List Seg) : List Bool := ss.flatMap segInput
def outputs (ss : List Seg) : List Bool := ss.flatMap segOutput
def costs (ss : List Seg) : Nat := (ss.map segCost).sum

def fwords : List Pair → List Bool
  | [] => []
  | p::ps => p.word.reverse ++ fwords ps
def effect : List Pair → List Bool
  | [] => []
  | p::ps => p.next [] ++ effect ps

theorem insAppend (a b : List Block) : ins (a++b)=ins a++ins b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [ins,ih,List.append_assoc]

theorem outsAppend (a b : List Block) : outs (a++b)=outs a++outs b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [outs,ih,List.append_assoc]

theorem insA (n : Nat) : ins (List.replicate n .a)=rep P n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ins,Block.inp,rep,P,ih]

theorem outsA (n : Nat) : outs (List.replicate n .a)=rep Q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,outs,Block.out,rep,Q,ih]

theorem fwordsAppend (a b : List Pair) : fwords (a++b)=fwords a++fwords b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [fwords,ih,List.append_assoc]

theorem effectAppend (a b : List Pair) : effect (a++b)=effect a++effect b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [effect,ih,List.append_assoc]

theorem fwordsZ1 (n : Nat) : fwords (List.replicate n .z1)=rep P n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fwords,List.replicate_succ,Pair.word,rep,P,ih]

theorem fwordsO0 (n : Nat) : fwords (List.replicate n .o0)=rep Q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fwords,List.replicate_succ,Pair.word,rep,Q,ih]

theorem effectZ1 (n : Nat) : effect (List.replicate n .z1)=rep P n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [effect,List.replicate_succ,Pair.next,rep,P,ih]

theorem effectO0 (n : Nat) : effect (List.replicate n .o0)=rep Q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [effect,List.replicate_succ,Pair.next,rep,Q,ih]

theorem fwordsReverse (ps : List Pair) : (fwords ps).reverse = pairWords ps.reverse := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have h : ∀ (a b : List Pair), pairWords (a++b)=pairWords a++pairWords b := by
      intro a b; induction a with
      | nil => rfl
      | cons x xs hi => simp [pairWords,hi,List.append_assoc]
    simp [fwords,List.reverse_cons,List.reverse_append,h,pairWords,ih]

theorem accEffect (ps : List Pair) (U : List Bool) :
    acc ps.reverse U=effect ps++U := by
  rw [accFormula,List.reverse_reverse]
  have h : (ps.map (fun p => p.next [])).flatten=effect ps := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [effect,ih]
  rw [h]

theorem rotateP (n : Nat) : [true]++rep Q n=rep P n++[true] := by
  simpa [P,Q] using rotate true [false] n

theorem rotateQ (n : Nat) : [false]++rep P n=rep Q n++[false] := by
  simpa [P,Q] using rotate false [true] n

theorem inputOne (s : Seg) : ins (segBlocks s)=segInput s := by
  rcases s with ⟨q,p⟩
  simp only [segBlocks,segInput,ins,insAppend,insA,Block.inp]
  simp only [rep, P,Q,List.cons_append,List.nil_append]
  have h := rotateP q
  simp only [P,Q,List.cons_append,List.nil_append] at h
  congr 3
  calc
    rep [true,false] q ++ [true,true,false] ++ rep [true,false] p =
      (rep [true,false] q ++ [true]) ++ [true,false] ++ rep [true,false] p := by simp [List.append_assoc]
    _ = _ := by rw [← h]; simp [List.append_assoc]

theorem outputOne (s : Seg) : effect (segPairs s)=segOutput s := by
  rcases s with ⟨q,p⟩
  simp only [segPairs,segOutput,effect,effectAppend,effectZ1,effectO0,Pair.next,Z,List.append_assoc]

theorem streamOne (s : Seg) : [true]++outs (segBlocks s)=fwords (segPairs s)++[true] := by
  rcases s with ⟨q,p⟩
  simp only [segBlocks,segPairs,outs,outsAppend,outsA,Block.out,fwords,fwordsAppend,
    fwordsZ1,fwordsO0,Pair.word,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.singleton_append,List.cons_append]
  simp only [rep,Q,List.cons_append,List.nil_append]
  congr 4
  calc
    rep [false,true] q ++ [false,true,true] ++ rep [false,true] p =
      (rep Q q ++ Q) ++ ([true]++rep Q p) := by simp [Q,List.append_assoc]
    _ = (Q ++ rep Q q) ++ (rep P p ++ [true]) := by rw [rep_snoc,rotateP]
    _ = _ := by simp [Q,List.append_assoc]

theorem inputMany (ss : List Seg) : ins (blocks ss)=inputs ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change ins (segBlocks s++blocks ss)=segInput s++inputs ss
    rw [insAppend,inputOne,ih]

theorem outputMany (ss : List Seg) : effect (pairs ss)=outputs ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change effect (segPairs s++pairs ss)=segOutput s++outputs ss
    rw [effectAppend,outputOne,ih]

theorem streamMany (ss : List Seg) : [true]++outs (blocks ss)=fwords (pairs ss)++[true] := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change [true]++outs (segBlocks s++blocks ss)=fwords (segPairs s++pairs ss)++[true]
    rw [outsAppend,fwordsAppend,← List.append_assoc [true],streamOne,List.append_assoc,ih,List.append_assoc]

theorem streamAll (a : Nat) (ss : List Seg) :
    [true]++outs (List.replicate a .a++blocks ss)=
    fwords (List.replicate a .z1++pairs ss)++[true] := by
  rw [outsAppend,outsA,fwordsAppend,fwordsZ1,← List.append_assoc [true],rotateP,List.append_assoc,streamMany,List.append_assoc]

theorem repLength (w : List Bool) (n : Nat) : (rep w n).length=w.length*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih,Nat.mul_succ,Nat.add_comm]

theorem costAppend (a b : List Pair) : pairCost (a++b)=pairCost a+pairCost b := by
  induction a with
  | nil => simp [pairCost]
  | cons p ps ih => simp [pairCost,ih,Nat.add_assoc]

theorem costReverse (ps : List Pair) : pairCost ps.reverse=pairCost ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.reverse_cons,costAppend,ih,pairCost,Nat.add_comm]

theorem costRep (p : Pair) (n : Nat) : pairCost (List.replicate n p)=p.cost*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,pairCost,ih,Nat.mul_succ,Nat.add_comm]

theorem costOne (s : Seg) : (segInput s).length+pairCost (segPairs s)=segCost s := by
  rcases s with ⟨q,p⟩
  simp [segInput,segPairs,segCost,repLength,P,Q,pairCost,costAppend,costRep,Pair.cost]
  omega

theorem costMany (ss : List Seg) : (inputs ss).length+pairCost (pairs ss)=costs ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change (segInput s++inputs ss).length+pairCost (segPairs s++pairs ss)=segCost s+costs ss
    rw [List.length_append,costAppend]
    have h := costOne s
    omega

/-- Exact even first return, independent of the untouched suffix. -/
theorem evenReturn (a : Nat) (ss : List Seg) (U : List Bool) :
    run0 table (4*a+costs ss+6)
      (frontier (rep P a++inputs ss++Z++U)) =
    some (frontier (rep P (a+1)++outputs ss++Q++U)) := by
  let bs := List.replicate a .a++blocks ss
  let ps := List.replicate a .z1++pairs ss
  have hstream := congrArg List.reverse (streamAll a ss)
  have hs : (outs bs).reverse++[true]=[true]++pairWords ps.reverse := by
    simpa only [bs,ps,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,fwordsReverse] using hstream
  have h : Turn.d.start++((outs bs).reverse++[true]) =
      Turn.d.pair++(pairWords ps.reverse++endStream false) := by
    rw [hs]
    simp [Turn.start,Turn.pair,endStream]
  have hi : ins bs=rep P a++inputs ss := by simp [bs,insAppend,insA,inputMany]
  have ho : effect ps=rep P a++outputs ss := by simp [ps,effectAppend,effectZ1,outputMany]
  have hc : (ins bs).length+Turn.d.inp.length+2+pairCost ps.reverse+2=4*a+costs ss+6 := by
    rw [hi,costReverse]
    simp only [ps,List.length_append,repLength,P,List.length_cons,List.length_nil,costAppend,costRep,Pair.cost,Turn.inp]
    have h := costMany ss
    omega
  have H := frontierReturn bs .d U ps.reverse false h
  rw [hc,hi,accEffect,ho] at H
  simpa only [Turn.inp,Turn.leftBit,Bool.not_false,Bool.not_true,P,Q,Z,rep,List.cons_append,List.nil_append,List.append_assoc] using H

theorem principalEven (a q p : Nat) (ss : List Seg) (U : List Bool) :
    run0 table (8*a+segCost (q,p)+costs ss+16)
      (frontier (rep P a++inputs ((q,p)::ss)++Z++U)) =
    some (frontier (rep P (a+2)++Q++rep Q (q+2)++rep P p++outputs ss++Q++U)) := by
  have h1 := evenReturn a ((q,p)::ss) U
  have h1' : run0 table (4*a+segCost (q,p)+costs ss+6)
      (frontier (rep P a++inputs ((q,p)::ss)++Z++U)) =
      some (frontier (rep P (a+1)++Z++(rep Q (q+2)++rep P p++outputs ss++Q++U))) := by
    simpa [costs,outputs,segOutput,List.append_assoc,Nat.add_assoc] using h1
  have h2 := evenReturn (a+1) [] (rep Q (q+2)++rep P p++outputs ss++Q++U)
  have h2' : run0 table (4*(a+1)+6)
      (frontier (rep P (a+1)++Z++(rep Q (q+2)++rep P p++outputs ss++Q++U))) =
      some (frontier (rep P (a+2)++Q++rep Q (q+2)++rep P p++outputs ss++Q++U)) := by
    simpa [inputs,outputs,costs,List.append_assoc] using h2
  have H := join0 h1' h2'
  rw [show 4*a+segCost (q,p)+costs ss+6+(4*(a+1)+6)=8*a+segCost (q,p)+costs ss+16 by omega] at H
  exact H

#print axioms evenReturn
#print axioms principalEven
end Regular
end BB6Coverage.Agent41F421
