"""Generate original-source witnesses for raw61 leaves 1344 and 1346.

Reuse the counter emitter's symbolic-word and proof-generation functions.
Search is untrusted; emitted finite phases and sweep lemmas are kernel checked.
"""
from pathlib import Path
import heapq
ROOT=Path(__file__).resolve().parent
shared=ROOT.parent/"agent48-raw63-counter"/"emit_counter.py"
scope={"__file__":str(shared)}
exec(shared.read_text().split("\nTABLES=",1)[0],scope)
def search(p,start,target,limit=500):
    seen=set();pq=[];seq=0
    def add(c,h):
        nonlocal seq
        if c in seen:return
        if sum(len(w) for w,t in c.l+c.r if not t)>200 or len(h)>250:return
        seen.add(c);seq+=1
        heapq.heappush(pq,(len(h),seq,c,h))
    add(start,[])
    for _ in range(3000):
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
                k,O=a
                w2=clean(lit(lp)+wr[1:])
                o2=clean(lit(op[:j])+repeat(O,tag)+lit(op[j:])+rest(o))
                dst=C(c.q,w2,o2) if sd=="L" else C(c.q,o2,w2)
                add(dst,h+[("loop",c,dst,k,sd,I,O,j,tag)])
        try:d=step(p,c)
        except ValueError:continue
        add(d,h+[("step",c,d,1)])
    return None
# Expose shared functions locally; replace the generator's greedy search.
globals().update({k:v for k,v in scope.items() if not k.startswith("__") and k!="ROOT"})
scope["pump"]=search
def D(s,t="",u=""):
    # s, followed by k copies of t, then u (literal suffix)
    return cfg(3,lit(s)+(repeat(t,"k") if t else ())+lit(u),())
def W(s,t,u,v):
    return cfg(3,lit(s)+(repeat(t,"k") if t else ())+lit(u)+(repeat(v,"n") if v else ()),())
phases=[
 ("first",W("0011","","","11"),W("000001","","","11")),
 ("odd",W("00000","000000","111","11"),W("00000000","000000","11","11")),
 ("even",W("00000000","000000","11","11"),W("00000000000","000000","1","11")),
 ("finish",D("00000","000000","1"),D("00111111","111111",""))]
tables={1344:"1RB1RF_1RC0LA_0RD0RC_1LD1RE_---0LB_0RF0RC",1346:"1RB1RF_1RC0LA_0RD1LF_1LD1RE_---0LB_0RF0RC"}
out=["import Agent48CounterCore","namespace BB6.Agent48Tripling","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false"]
for i,s in tables.items():
    p=tuple(parse(s));out += [f"namespace M{i}",table(p)]
    a,b,c=(16,22,12) if i==1344 else (22,34,24)
    for (name,st,tg),expected in zip(phases,[(10,0,0),(a,0,c),(b,0,c),(23,0,24)]):
        out.append(macro(p,name,st,tg,("k","n"),expected)[0])
    out.append(f"""
def outer (n : Nat) : Z0 := ⟨3,[false,false] ++ rep [true,true] (n+1),[]⟩
def inner (k n : Nat) : Z0 := ⟨3,[false,false,false,false,false] ++ rep [false,false,false,false,false,false] k ++ [true] ++ rep [true,true] n,[]⟩
theorem pair (k n : Nat) : run0 table (({a}+{c}*k)+({b}+{c}*k)) (inner k (n+1)) = some (inner (k+1) n) := by
  have h1 := odd k n
  have h2 := even k n
  have h := join0 h1 h2
  simpa only [inner,rep,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.add_zero] using h
theorem drain (n k : Nat) : ∃ t, run0 table t (inner k n) = some (inner (k+n) 0) := by
  induction n generalizing k with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih (k+1)
    refine ⟨({a}+{c}*k)+({b}+{c}*k)+t,?_⟩
    have h := join0 (pair k n) ht
    rw [show k+1+n=k+(n+1) by omega] at h
    exact h
theorem repSix (k : Nat) : rep [true,true,true,true,true,true] k = rep [true,true] (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 3*(k+1)=3*k+3 by omega]
    simp only [rep,ih,List.cons_append,List.nil_append]
theorem progressOuter (n : Nat) : ∃ t, 0 < t ∧ run0 table t (outer n) = some (outer (3*n+2)) := by
  have h1 : run0 table 10 (outer n) = some (inner 0 n) := by
    simpa only [outer,inner,rep,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.add_zero] using first 0 n
  obtain ⟨t,ht⟩ := drain n 0
  simp only [Nat.zero_add] at ht
  have h2 : run0 table (23+24*n) (inner n 0) = some (outer (3*n+2)) := by
    have h := finish n 0
    rw [repSix] at h
    simpa only [inner,outer,rep,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.add_zero,Nat.add_assoc] using h
  exact ⟨10+t+(23+24*n),by omega,join0 (join0 h1 ht) h2⟩
theorem entry : run0 table 36 ⟨0,[],[]⟩ = some (outer 2) := by rfl
def invariant (z : Z0) : Prop := ∃ n, z = outer n
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0 < t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨n,rfl⟩ := hz
  obtain ⟨t,hp,ht⟩ := progressOuter n
  exact ⟨t,outer (3*n+2),hp,ht,3*n+2,rfl⟩
theorem live (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ invariant z :=
  arbitraryLive_of_progress table invariant 36 (outer 2) entry ⟨2,rfl⟩ progress n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 36 (outer 2) entry ⟨2,rfl⟩ progress m hm
#print axioms never
end M{i}""")
out.append("end BB6.Agent48Tripling")
(ROOT/"Agent48Raw61Tripling.lean").write_text("\n\n".join(out)+"\n")
