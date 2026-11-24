"""Generate a recursive word-language nonhalting certificate for raw61 leaf 353."""
from pathlib import Path
import heapq
ROOT=Path(__file__).resolve().parent
shared=ROOT.parent/"agent48-raw63-counter"/"emit_counter.py"
scope={"__file__":str(shared)}
prefix_code=shared.read_text().split("\nTABLES=",1)[0]
exec(prefix_code.replace("if x=='S' else 'Nat'","if x in ('L','R') else 'Nat'"),scope)
globals().update({k:v for k,v in scope.items() if not k.startswith("__") and k!="ROOT"})
def search(p,start,target,limit=500):
    seen=set();pq=[];seq=0
    def add(c,h):
        nonlocal seq
        if c in seen:return
        if sum(len(w) for w,t in c.l+c.r if not t)>200 or len(h)>250:return
        seen.add(c);seq+=1
        heapq.heappush(pq,(len(h),seq,c,h))
    add(start,[])
    for _ in range(10000):
        if not pq:return None
        _,_,c,h=heapq.heappop(pq)
        if c.norm()==target.norm():return h,c
        for sd in ["L","R"]:
            w,o=(c.l,c.r) if sd=="L" else (c.r,c.l)
            lp=prefix(w);wr=rest(w);op=prefix(o)
            if not wr:continue
            I,tag=wr[0]
            if tag=="S":continue
            for j in range(min(20,len(op))+1):
                a=local(p,c.q,lp if sd=="L" else op[:j],op[:j] if sd=="L" else lp,sd,I)
                if not a:continue
                k,O=a;w2=clean(lit(lp)+wr[1:])
                o2=clean(lit(op[:j])+repeat(O,tag)+lit(op[j:])+rest(o))
                dst=C(c.q,w2,o2) if sd=="L" else C(c.q,o2,w2)
                add(dst,h+[("loop",c,dst,k,sd,I,O,j,tag)])
        try:d=step(p,c)
        except ValueError:continue
        add(d,h+[("step",c,d,1)])
    return None
scope["pump"]=search
def word2(w):
    return app(*[("L" if s=="X" else "R") if t=="S" else (f"rep {bits(s)} {t}" if t else bits(s)) for s,t in w])
scope["word"]=word2
p=tuple(parse("1RB0LF_1RC0LA_0RD---_1LD1RE_0RC0LB_0RB1LE"))
P=repeat("1111","n");Z=repeat("0001","n");SX=repeat("X","S");TY=repeat("Y","S")
phases=[
("term0",cfg(3,lit("001111")+P,TY),cfg(3,lit("101"),lit("0001")+Z+TY),("n","R"),(10,4,0)),
("term1",cfg(3,lit("0011111")+P,TY),cfg(3,lit("1011"),lit("0001")+Z+TY),("n","R"),(12,4,0)),
("term2",cfg(3,lit("00111111")+P,TY),cfg(3,lit("001111"),lit("001")+Z+TY),("n","R"),(27,4,0)),
("zero",cfg(3,lit("00111111")+P+lit("0")+SX,TY),cfg(3,lit("001111")+SX,lit("001")+Z+TY),("n","L","R"),(27,4,0)),
("marker",cfg(3,lit("001111")+P+lit("010")+SX,TY),cfg(3,lit("10110")+SX,lit("0001")+Z+TY),("n","L","R"),(10,4,0))]
out=["import Agent48CounterCore","namespace BB6.Agent48Language353","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",table(p)]
for name,st,tg,params,cost in phases:out.append(macro(p,name+"Macro",st,tg,params,cost)[0])
out.append("""
def P := [true,true,true,true]
def T := [false,false,false,true]
def M := [false,false,true]
def Z := [true,true,false]
def J := [false,true,false]
def F (w R : List Bool) : Z0 := ⟨3,[false,false]++w,R⟩
def G (w R : List Bool) : Z0 := ⟨3,[true,false]++w,R⟩
inductive Good : List Bool → Prop where
  | nil : Good []
  | one : Good [true]
  | two : Good [true,true]
  | four {w} : Good w → Good (P++w)
  | zero {w} : Good w → Good (Z++w)
  | marker {w} : Good w → Good (J++w)

theorem goodRep (n : Nat) {w : List Bool} (h : Good w) : Good (rep P n++w) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [rep,List.append_assoc] using Good.four ih

theorem oneComm (n : Nat) : rep P n ++ [true] = [true] ++ rep P n := by
  simpa [P] using (rotate true [true,true,true] n).symm
theorem twoComm (n : Nat) : rep P n ++ [true,true] = [true,true] ++ rep P n := by
  change rep P n ++ ([true]++[true]) = [true]++([true]++rep P n)
  rw [← List.append_assoc,oneComm,List.append_assoc,oneComm]

theorem transfer (w R : List Bool) : run0 table 18 (G w (T++R)) = some (G (P++w) R) := by rfl
theorem insert (w R : List Bool) : run0 table 3 (G w (M++R)) = some (G (J++w) R) := by rfl
theorem extend (w : List Bool) : run0 table 18 (G w []) = some (F (P++w) []) := by rfl

theorem drain (n : Nat) (w R : List Bool) :
    run0 table (18*n) (G w (rep T n++R)) = some (G (rep P n++w) R) := by
  induction n generalizing w with
  | zero => simp [run0,rep]
  | succ n ih =>
    have h1 := transfer w (rep T n++R)
    have h2 := ih (P++w)
    have h := join0 h1 h2
    rw [Nat.mul_succ,Nat.add_comm (18*n) 18]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep P n) P w,rep_snoc P n] using h

def Resolves (w R : List Bool) : Prop :=
  ∃ w', Good w' ∧ Reaches table (F w R) (G w' R)

theorem resolveTerm0 (n : Nat) (R : List Bool) : Resolves (rep P (n+1)++[]) R := by
  have h1 : run0 table (10+4*n) (F (rep P (n+1)++[]) R) =
      some (G [true] (rep T (n+1)++R)) := by
    simpa only [F,G,P,T,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using term0Macro n R
  have h2 := drain (n+1) [true] R
  exact ⟨_,goodRep (n+1) Good.one,_,join0 h1 h2⟩

theorem resolveTerm1 (n : Nat) (R : List Bool) : Resolves (rep P (n+1)++[true]) R := by
  have h1 : run0 table (12+4*n) (F (rep P (n+1)++[true]) R) =
      some (G [true,true] (rep T (n+1)++R)) := by
    rw [oneComm]
    simpa only [F,G,P,T,rep,List.append_assoc,List.cons_append,List.nil_append] using term1Macro n R
  have h2 := drain (n+1) [true,true] R
  exact ⟨_,goodRep (n+1) Good.two,_,join0 h1 h2⟩

theorem restore (n : Nat) (w R : List Bool) (hw : Good w) :
    ∃ w', Good w' ∧ Reaches table (G w (M++rep T n++R)) (G w' R) := by
  have h1 := insert w (rep T n++R)
  have h2 := drain n (J++w) R
  exact ⟨_,goodRep n (Good.marker hw),_,by simpa only [List.append_assoc] using join0 h1 h2⟩

theorem resolveTerm2 (n : Nat) (R : List Bool) : Resolves (rep P (n+1)++[true,true]) R := by
  have h1 : run0 table (27+4*n) (F (rep P (n+1)++[true,true]) R) =
      some (F (P++[]) (M++rep T n++R)) := by
    rw [twoComm]
    simpa only [F,P,M,T,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using term2Macro n R
  obtain ⟨w,hw,t,ht⟩ := resolveTerm0 0 (M++rep T n++R)
  obtain ⟨w',hw',u,hu⟩ := restore n w R hw
  exact ⟨w',hw',_,join0 (join0 h1 ht) hu⟩

theorem resolve {w : List Bool} (hw : Good w) (n : Nat) (R : List Bool) :
    Resolves (rep P (n+1)++w) R := by
  induction hw generalizing n R with
  | nil => exact resolveTerm0 n R
  | one => exact resolveTerm1 n R
  | two => exact resolveTerm2 n R
  | four h ih =>
    have h' := ih (n+1) R
    simpa only [rep_right P (n+1),List.append_assoc] using h'
  | @zero w h ih =>
    have h1 : run0 table (27+4*n) (F (rep P (n+1)++(Z++w)) R) =
        some (F (P++w) (M++rep T n++R)) := by
      have hh : rep P (n+1)++(Z++w) = [true,true]++rep P (n+1)++[false]++w := by
        change rep P (n+1)++([true,true]++[false]++w) = _
        rw [← List.append_assoc,← List.append_assoc,twoComm]
      rw [hh]
      simpa only [F,P,M,T,rep,List.append_assoc,List.cons_append,List.nil_append] using zeroMacro n w R
    obtain ⟨w',hw',t,ht⟩ := ih 0 (M++rep T n++R)
    obtain ⟨w'',hw'',u,hu⟩ := restore n w' R hw'
    exact ⟨w'',hw'',_,join0 (join0 h1 ht) hu⟩
  | @marker w h ih =>
    have h1 : run0 table (10+4*n) (F (rep P (n+1)++(J++w)) R) =
        some (G (Z++w) (rep T (n+1)++R)) := by
      simpa only [F,G,P,T,Z,J,rep,List.append_assoc,List.cons_append,List.nil_append] using markerMacro n w R
    have h2 := drain (n+1) (Z++w) R
    exact ⟨_,goodRep (n+1) (Good.zero h),_,join0 h1 h2⟩

def invariant (z : Z0) : Prop := ∃ w, Good w ∧ z = F (P++w) []
theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (F (P++[]) []) := by rfl
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨w,hw,rfl⟩ := hz
  obtain ⟨w',hw',t,ht⟩ := resolve hw 0 []
  have he := extend w'
  exact ⟨t+18,_,by omega,join0 ht he,w',hw',rfl⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 26 (F (P++[]) []) entry ⟨[],Good.nil,rfl⟩ progress m hm
#print axioms never
end BB6.Agent48Language353
""")
(ROOT/"Agent48Raw61Language353.lean").write_text("\n\n".join(out)+"\n")
