import F421Regular

namespace BB6Coverage.Agent41F421.Regular
open BB6Coverage Agent31Pump

structure Cell where
  p : Nat
  q : Nat
  deriving DecidableEq, Repr

def validCell (c : Cell) : Prop := 1 ≤ c.p ∧ 2 ≤ c.q

def valid (cs : List Cell) : Prop := ∀ c ∈ cs, validCell c

def cellWord (marked : Bool) (c : Cell) : List Bool :=
  rep P c.p ++ (if marked then Z else []) ++ rep Q c.q

def nearWord (marked : Bool) : List Cell → List Bool
  | [] => []
  | c::cs => cellWord marked c ++ nearWord marked cs

def dec (cs : List Cell) : List Cell := cs.map (fun c => ⟨c.p-1,c.q⟩)

def segs (b : Nat) (cs : List Cell) (p : Nat) : List Seg :=
  match cs with
  | [] => [(b-2,p-1)]
  | c::cs => (b-2,c.p-1)::segs c.q cs p

theorem repAdd (w : List Bool) (a b : Nat) : rep w (a+b)=rep w a++rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega]
    simp [rep,ih,List.append_assoc]

theorem inputSegs (b : Nat) (cs : List Cell) (p : Nat)
    (hb : 2 ≤ b) (hp : 1 ≤ p) (hv : valid cs) :
    inputs (segs b cs p)=rep Q b++nearWord false cs++rep P p := by
  induction cs generalizing b with
  | nil =>
    simp [segs,inputs,segInput,nearWord,show b-2+2=b by omega,show p-1+1=p by omega]
  | cons c cs ih =>
    have hc := hv c (by simp)
    have ht : valid cs := by intro x hx; exact hv x (by simp [hx])
    have h := ih c.q hc.2 ht
    change segInput (b-2,c.p-1)++inputs (segs c.q cs p)=_
    rw [h]
    simp [segInput,nearWord,cellWord,show b-2+2=b by omega,
      show c.p-1+1=c.p by unfold validCell at hc; omega,List.append_assoc]

theorem outputSegs (b : Nat) (cs : List Cell) (p : Nat)
    (hb : 2 ≤ b) (hv : valid cs) :
    outputs (segs b cs p)=Z++rep Q b++nearWord true (dec cs)++rep P (p-1) := by
  induction cs generalizing b with
  | nil => simp [segs,outputs,segOutput,nearWord,dec,show b-2+2=b by omega,List.append_assoc]
  | cons c cs ih =>
    have hc := hv c (by simp)
    have ht : valid cs := by intro x hx; exact hv x (by simp [hx])
    have h := ih c.q hc.2 ht
    change segOutput (b-2,c.p-1)++outputs (segs c.q cs p)=_
    rw [h]
    simp [segOutput,nearWord,dec,cellWord,show b-2+2=b by omega,List.append_assoc]

/-- Carry through arbitrary unmarked cells to a marked terminal cell. -/
theorem carryAcross (a b : Nat) (cs : List Cell) (p : Nat) (U : List Bool)
    (hb : 2 ≤ b) (hp : 1 ≤ p) (hv : valid cs) :
    run0 table (8*a+costs (segs b cs p)+16)
      (frontier (rep P a++rep Q b++nearWord false cs++rep P p++Z++U)) =
    some (frontier (rep P (a+2)++rep Q (b+1)++nearWord true (dec cs)++rep P (p-1)++Q++U)) := by
  have h1 := evenReturn a (segs b cs p) U
  rw [inputSegs b cs p hb hp hv, outputSegs b cs p hb hv] at h1
  let W := rep Q b++nearWord true (dec cs)++rep P (p-1)++Q++U
  have h1' : run0 table (4*a+costs (segs b cs p)+6)
      (frontier (rep P a++rep Q b++nearWord false cs++rep P p++Z++U)) =
      some (frontier (rep P (a+1)++Z++W)) := by
    simpa [W,List.append_assoc] using h1
  have h2 := evenReturn (a+1) [] W
  have h2' : run0 table (4*(a+1)+6) (frontier (rep P (a+1)++Z++W)) =
      some (frontier (rep P (a+2)++Q++W)) := by
    simpa [inputs,outputs,costs,List.append_assoc] using h2
  have H := join0 h1' h2'
  rw [show 4*a+costs (segs b cs p)+6+(4*(a+1)+6)=8*a+costs (segs b cs p)+16 by omega] at H
  simpa [W,rep,List.append_assoc] using H

def farWord (marked : Bool) (cs : List Cell) : List Bool := nearWord marked cs.reverse

theorem nearAppend (marked : Bool) (xs ys : List Cell) :
    nearWord marked (xs++ys)=nearWord marked xs++nearWord marked ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [nearWord,ih,List.append_assoc]

theorem farCons (marked : Bool) (c : Cell) (cs : List Cell) :
    farWord marked (c::cs)=farWord marked cs++cellWord marked c := by
  simp [farWord,List.reverse_cons,nearAppend,nearWord]

theorem decReverse (cs : List Cell) : dec cs.reverse=(dec cs).reverse := by
  simp [dec,List.map_reverse]

def budget (B : Nat) : List Cell → Prop
  | [] => True
  | c::cs => 2*B-1 ≤ c.p ∧ 2 ≤ c.q ∧ budget (2*B) cs

def finishCells (B : Nat) : List Cell → List Cell
  | [] => []
  | c::cs => ⟨c.p-(2*B-1),c.q+B⟩::finishCells (2*B) cs

theorem budgetWeaken (B C : Nat) (cs : List Cell) (hBC : B ≤ C)
    (h : budget C cs) : budget B cs := by
  induction cs generalizing B C with
  | nil => trivial
  | cons c cs ih =>
    rcases h with ⟨hp,hq,ht⟩
    exact ⟨by omega,hq,ih (2*B) (2*C) (by omega) ht⟩

theorem budgetValid (B : Nat) (cs : List Cell) (hB : 1 ≤ B)
    (h : budget B cs) : valid cs := by
  induction cs generalizing B with
  | nil => simp [valid]
  | cons c cs ih =>
    rcases h with ⟨hp,hq,ht⟩
    intro x hx
    rcases List.mem_cons.mp hx with he|hm
    · subst x; exact ⟨by omega,hq⟩
    · exact ih (2*B) (by omega) ht x hm

theorem afterHalf (B : Nat) (cs : List Cell) (hB : 1 ≤ B)
    (h : budget (2*B) cs) :
    valid (finishCells B cs) ∧ budget B (dec (finishCells B cs)) := by
  induction cs generalizing B with
  | nil => exact ⟨by simp [finishCells,valid],trivial⟩
  | cons c cs ih =>
    rcases h with ⟨hp,hq,ht⟩
    have h' : budget (2*(2*B)) cs := by simpa [Nat.mul_assoc] using ht
    obtain ⟨hv,hb⟩ := ih (2*B) (by omega) h'
    constructor
    · intro x hx
      rw [finishCells,List.mem_cons] at hx
      rcases hx with he|hm
      · subst x; exact ⟨by change 1 ≤ c.p-(2*B-1); omega,by change 2 ≤ c.q+B; omega⟩
      · exact hv x hm
    · change 2*B-1 ≤ c.p-(2*B-1)-1 ∧ 2 ≤ c.q+B ∧ budget (2*B) (dec (finishCells (2*B) cs))
      exact ⟨by omega,by omega,hb⟩

theorem finishTwice (B : Nat) (cs : List Cell) (hB : 1 ≤ B) :
    finishCells B (dec (finishCells B cs))=finishCells (2*B) cs := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih =>
    change Cell.mk (c.p-(2*B-1)-1-(2*B-1)) (c.q+B+B) ::
      finishCells (2*B) (dec (finishCells (2*B) cs)) =
      Cell.mk (c.p-(2*(2*B)-1)) (c.q+2*B) :: finishCells (2*(2*B)) cs
    rw [ih (2*B) (by omega)]
    congr 2 <;> omega

theorem finishLength (B : Nat) (cs : List Cell) : (finishCells B cs).length=cs.length := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih => simp [finishCells,ih]

theorem decLength (cs : List Cell) : (dec cs).length=cs.length := by simp [dec]

def macroCount (cs : List Cell) : Nat := 2^cs.length-1

theorem macroCountCons (c : Cell) (cs : List Cell) : macroCount (c::cs)=2*macroCount cs+1 := by
  have hp : 0 < 2^cs.length := Nat.pow_pos (by decide)
  simp only [macroCount,List.length_cons,Nat.pow_succ]
  omega

/-- The full all-marked drain is an unbounded source-machine computation.
    It works even when terminal P runs disappear. The endpoint retains
    zero-P cells as empty words. -/
theorem allMarkedDrain (cs : List Cell) (a b : Nat) (U : List Bool)
    (hb : 2 ≤ b) (h : budget 1 cs) :
    ∃ n, macroCount cs ≤ n ∧ run0 table n
      (frontier (rep P a++rep Q b++farWord true cs++U)) =
      some (frontier (rep P (a+2*macroCount cs)++rep Q (b+macroCount cs)++farWord false (finishCells 1 cs)++U)) := by
  cases cs with
  | nil => exact ⟨0,by simp [macroCount],by simp [macroCount,farWord,nearWord,finishCells,run0]⟩
  | cons c cs =>
    rcases h with ⟨hp,hq,ht⟩
    have hp' : 1 ≤ c.p := by omega
    let K := macroCount cs
    let L1 := finishCells 1 cs
    let L2 := dec L1
    let U1 := cellWord false ⟨c.p-1,c.q+1⟩++U
    have hlow : budget 1 cs := budgetWeaken 1 2 cs (by decide) ht
    obtain ⟨n1,hn1,hr1⟩ := allMarkedDrain cs a b (cellWord true c++U) hb hlow
    obtain ⟨hv,hb2⟩ := afterHalf 1 cs (by decide) ht
    have hv' : valid L1.reverse := by
      intro x hx
      exact hv x (List.mem_reverse.mp hx)
    have hr2 := carryAcross (a+2*K) (b+K) L1.reverse c.p (rep Q c.q++U) (by omega) hp' hv'
    let n2 := 8*(a+2*K)+costs (segs (b+K) L1.reverse c.p)+16
    have hr1' : run0 table n1 (frontier (rep P a++rep Q b++farWord true (c::cs)++U)) =
        some (frontier (rep P (a+2*K)++rep Q (b+K)++farWord false L1++rep P c.p++Z++rep Q c.q++U)) := by
      simpa [K,L1,farCons,cellWord,List.append_assoc] using hr1
    have hr2' : run0 table n2
        (frontier (rep P (a+2*K)++rep Q (b+K)++farWord false L1++rep P c.p++Z++rep Q c.q++U)) =
        some (frontier (rep P (a+2*K+2)++rep Q (b+K+1)++farWord true L2++U1)) := by
      simpa [n2,L2,U1,farWord,decReverse,cellWord,rep,List.append_assoc] using hr2
    obtain ⟨n3,hn3,hr3⟩ := allMarkedDrain L2 (a+2*K+2) (b+K+1) U1 (by omega) hb2
    have hk : macroCount L2=K := by simp [L2,L1,K,macroCount,decLength,finishLength]
    have hf : finishCells 1 L2=finishCells 2 cs := finishTwice 1 cs (by decide)
    have hK : macroCount (c::cs)=2*K+1 := macroCountCons c cs
    have ha : a+2*K+2+2*macroCount L2=a+2*macroCount (c::cs) := by omega
    have hB : b+K+1+macroCount L2=b+macroCount (c::cs) := by omega
    have hr3' : run0 table n3 (frontier (rep P (a+2*K+2)++rep Q (b+K+1)++farWord true L2++U1)) =
        some (frontier (rep P (a+2*macroCount (c::cs))++rep Q (b+macroCount (c::cs))++farWord false (finishCells 1 (c::cs))++U)) := by
      rw [ha,hB,hf] at hr3
      simpa [finishCells,farCons,U1,List.append_assoc] using hr3
    refine ⟨n1+n2+n3,?_,join0 (join0 hr1' hr2') hr3'⟩
    change K ≤ n1 at hn1
    rw [hk] at hn3
    dsimp [n2]
    omega
termination_by cs.length
decreasing_by
  all_goals simp_all [L2,L1,decLength,finishLength]

#print axioms carryAcross
#print axioms allMarkedDrain

end BB6Coverage.Agent41F421.Regular
