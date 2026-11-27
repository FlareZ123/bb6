import F421Drain

namespace BB6Coverage.Agent41F421.Regular
open BB6Coverage Agent31Pump

def oddPairsOne (s : Seg) : List Pair :=
  List.replicate (s.1+2) .z1++[.o1]++List.replicate s.2 .o0
def oddOutputOne (s : Seg) : List Bool := rep P (s.1+2)++Z++rep Q s.2
def oddCostOne (s : Seg) : Nat := 4*(s.1+2)+8*s.2+4

def oddPairs (ss : List Seg) : List Pair := ss.flatMap oddPairsOne
def oddOutputs (ss : List Seg) : List Bool := ss.flatMap oddOutputOne
def oddCosts (ss : List Seg) : Nat := (ss.map oddCostOne).sum

theorem oddStreamOne (s : Seg) : outs (segBlocks s)=fwords (oddPairsOne s) := by
  rcases s with ⟨q,p⟩
  simp only [segBlocks,oddPairsOne,outs,outsAppend,outsA,Block.out,fwordsAppend,
    fwordsZ1,fwordsO0,fwords,Pair.word,List.reverse_cons,List.reverse_nil,List.nil_append,
    rep,P,List.cons_append]
  congr 2
  change [true]++(rep Q q++[false,true,true]++rep Q p) =
    P++(rep P q++[true,true]++rep Q p)
  calc
    _ = ([true]++rep Q q)++[false,true,true]++rep Q p := by simp [List.append_assoc]
    _ = (rep P q++P)++[true,true]++rep Q p := by rw [rotateP]; simp [P,List.append_assoc]
    _ = _ := by rw [rep_snoc]; simp [List.append_assoc]

theorem oddEffectOne (s : Seg) : effect (oddPairsOne s)=oddOutputOne s := by
  rcases s with ⟨q,p⟩
  simp [oddPairsOne,oddOutputOne,effectAppend,effectZ1,effectO0,effect,Pair.next,Z,List.append_assoc]

theorem oddStreamMany (ss : List Seg) : outs (blocks ss)=fwords (oddPairs ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change outs (segBlocks s++blocks ss)=fwords (oddPairsOne s++oddPairs ss)
    rw [outsAppend,fwordsAppend,oddStreamOne,ih]

theorem oddEffectMany (ss : List Seg) : effect (oddPairs ss)=oddOutputs ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change effect (oddPairsOne s++oddPairs ss)=oddOutputOne s++oddOutputs ss
    rw [effectAppend,oddEffectOne,ih]

theorem oddCostEq (s : Seg) : (segInput s).length+pairCost (oddPairsOne s)=oddCostOne s := by
  rcases s with ⟨q,p⟩
  simp [segInput,oddPairsOne,oddCostOne,repLength,P,Q,pairCost,costAppend,costRep,Pair.cost]
  omega

theorem oddCostMany (ss : List Seg) : (inputs ss).length+pairCost (oddPairs ss)=oddCosts ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change (segInput s++inputs ss).length+pairCost (oddPairsOne s++oddPairs ss)=oddCostOne s+oddCosts ss
    rw [List.length_append,costAppend]
    have h := oddCostEq s
    omega

def E : List Bool := [false,true,true]

theorem principalOddE (a : Nat) (ss : List Seg) (U : List Bool) :
    run0 table (8*a+oddCosts ss+13)
      (frontier (rep P a++inputs ss++E++U)) =
    some (frontier (P++rep Q (a+1)++oddOutputs ss++P++U)) := by
  let bs := List.replicate a .a++blocks ss
  let ps := List.replicate a .o0++oddPairs ss
  have hs : outs bs=fwords ps := by
    simp [bs,ps,outsAppend,outsA,fwordsAppend,fwordsO0,oddStreamMany]
  have h : Turn.e.start++((outs bs).reverse++[true]) =
      Turn.e.pair++(pairWords ps.reverse++endStream true) := by
    rw [hs,fwordsReverse]
    rfl
  have hi : ins bs=rep P a++inputs ss := by simp [bs,insAppend,insA,inputMany]
  have ho : effect ps=rep Q a++oddOutputs ss := by simp [ps,effectAppend,effectO0,oddEffectMany]
  have hc : (ins bs).length+Turn.e.inp.length+2+pairCost ps.reverse+2=8*a+oddCosts ss+7 := by
    rw [hi,costReverse]
    simp only [ps,List.length_append,repLength,P,List.length_cons,List.length_nil,costAppend,costRep,Pair.cost,Turn.inp]
    have h := oddCostMany ss
    omega
  have h1 := frontierReturn bs .e U ps.reverse true h
  rw [hc,hi,accEffect,ho] at h1
  let W := rep Q a++oddOutputs ss++P++U
  have h1' : run0 table (8*a+oddCosts ss+7)
      (frontier (rep P a++inputs ss++E++U)) = some (frontier (Z++W)) := by
    simpa [W,Turn.inp,Turn.leftBit,E,P,Z,List.append_assoc] using h1
  have h2 : run0 table 6 (frontier (Z++W))=some (frontier (P++Q++W)) := by
    simpa [rep,inputs,outputs,costs,List.append_assoc] using evenReturn 0 [] W
  have H := join0 h1' h2
  simpa [W,rep,List.append_assoc,Nat.add_assoc] using H

def bridgeBlocks (q : Nat) : List Block := .c::List.replicate q .a

theorem bridgeInput (q : Nat) : ins (bridgeBlocks q)=rep Q (q+1)++[false] := by
  simp only [bridgeBlocks,ins,insA,Block.inp,rep,Q,List.cons_append,List.nil_append]
  congr 2
  simpa [P,Q] using rotateQ q

theorem bridgeStream (q : Nat) : outs (bridgeBlocks q)=
    fwords (List.replicate (q+1) .z1)++[true] := by
  simp only [bridgeBlocks,outs,outsA,Block.out,fwordsZ1,rep,P,List.cons_append,List.nil_append]
  congr 2
  simpa [P,Q] using rotateP q

def twistInputOne (s : Seg) : List Bool :=
  [false]++rep P (s.1+1)++R++rep Q s.2++[false]
def twistInputs (ss : List Seg) : List Bool := ss.flatMap twistInputOne

theorem twistInputEq (s : Seg) : ins (segBlocks s)=twistInputOne s := by
  rcases s with ⟨q,p⟩
  simp only [segBlocks,twistInputOne,ins,insAppend,insA,Block.inp,rep,P,R,List.cons_append,List.nil_append,List.append_assoc]
  congr 3
  have h := congrArg (fun w => rep [true,false] q ++ [true,true] ++ w) (rotateQ p)
  simpa [P,Q,List.append_assoc] using h

theorem twistInputMany (ss : List Seg) : ins (blocks ss)=twistInputs ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change ins (segBlocks s++blocks ss)=twistInputOne s++twistInputs ss
    rw [insAppend,twistInputEq,ih]

theorem twistCostEq (ss : List Seg) : (twistInputs ss).length+pairCost (pairs ss)=costs ss := by
  have e : (twistInputs ss).length=(inputs ss).length := by
    rw [← twistInputMany,← inputMany]
  rw [e]
  exact costMany ss

theorem principalOddD (a : Nat) (ss : List Seg) (q : Nat) (ts : List Seg) (U : List Bool) :
    run0 table (8*a+oddCosts ss+4*(q+1)+costs ts+13)
      (frontier (rep P a++inputs ss++rep Q (q+1)++[false]++twistInputs ts++Z++U)) =
    some (frontier (P++rep Q (a+1)++oddOutputs ss++rep P (q+1)++outputs ts++Q++U)) := by
  let bs := List.replicate a .a++blocks ss++bridgeBlocks q++blocks ts
  let ps := List.replicate a .o0++oddPairs ss++List.replicate (q+1) .z1++pairs ts
  have hs : outs bs=fwords ps++[true] := by
    simp only [bs,ps,outsAppend,outsA,bridgeStream,fwordsAppend,fwordsO0]
    rw [oddStreamMany ss]
    simp only [List.append_assoc]
    rw [streamMany ts]
  have hrev := congrArg List.reverse hs
  have hrev' : (outs bs).reverse=[true]++pairWords ps.reverse := by
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,fwordsReverse] using hrev
  have h : Turn.d.start++((outs bs).reverse++[true]) =
      Turn.d.pair++(pairWords ps.reverse++endStream true) := by
    rw [hrev']
    simp [Turn.start,Turn.pair,endStream,List.append_assoc]
  have hi : ins bs=rep P a++inputs ss++rep Q (q+1)++[false]++twistInputs ts := by
    simp only [bs,insAppend,insA,inputMany ss,bridgeInput,twistInputMany ts,List.append_assoc]
  have ho : effect ps=rep Q a++oddOutputs ss++rep P (q+1)++outputs ts := by
    simp [ps,effectAppend,effectO0,effectZ1,oddEffectMany,outputMany,List.append_assoc]
  have hc : (ins bs).length+Turn.d.inp.length+2+pairCost ps.reverse+2=8*a+oddCosts ss+4*(q+1)+costs ts+7 := by
    rw [hi,costReverse]
    simp only [ps,List.length_append,repLength,P,Q,List.length_cons,List.length_nil,costAppend,costRep,Pair.cost,Turn.inp]
    have h := oddCostMany ss
    have ht := twistCostEq ts
    omega
  have h1 := frontierReturn bs .d U ps.reverse true h
  rw [hc,hi,accEffect,ho] at h1
  let W := rep Q a++oddOutputs ss++rep P (q+1)++outputs ts++Q++U
  have h1' : run0 table (8*a+oddCosts ss+4*(q+1)+costs ts+7)
      (frontier (rep P a++inputs ss++rep Q (q+1)++[false]++twistInputs ts++Z++U)) =
      some (frontier (Z++W)) := by
    simpa [W,Turn.inp,Turn.leftBit,Z,Q,List.append_assoc] using h1
  have h2 : run0 table 6 (frontier (Z++W))=some (frontier (P++Q++W)) := by
    simpa [rep,inputs,outputs,costs,List.append_assoc] using evenReturn 0 [] W
  have H := join0 h1' h2
  simpa [W,rep,List.append_assoc,Nat.add_assoc] using H

#print axioms principalOddE
#print axioms principalOddD
end BB6Coverage.Agent41F421.Regular
