"""Regenerate exact recursive-fill growth proofs from fixed unary families.

A run is (bit, coefficient, constant), denoting bit^(coefficient*n+constant).
Symbolic steps are only discovery/decomposition; Lean independently checks every
fixed transition, local sweep, recursive fill and composed epoch.
"""
import json
from pathlib import Path
from dataclasses import dataclass
from itertools import groupby

ROOT=Path(__file__).resolve().parent

def parse(s):
    s=s.replace("_","")
    return tuple(s[j:j+3] for j in range(0,36,3))

def norm(w):
    out=[]
    for x,a,b in w:
        if a==b==0:continue
        if out and x==out[-1][0]:
            _,c,d=out.pop();out.append((x,a+c,b+d))
        else:out.append((x,a,b))
    return tuple(out)

def word(s):return tuple((int(b),0,len(list(g))) for b,g in groupby(s))
def prepend(w,*xs):return norm((*xs,*w))

def pop(w):
    if not w:return 0,()
    x,a,b=w[0]
    if b==0:raise ValueError("ambiguous pop")
    return x,norm(((x,a,b-1),*w[1:]))

def subrun(w,a,b):
    x,c,d=w[0];assert c>=a and d>=b
    return norm(((x,c-a,d-b),*w[1:]))

@dataclass(frozen=True)
class C:
    q:int
    l:tuple
    r:tuple

def primitive(p,c):
    x,lt=pop(c.l);m=p[2*c.q+x]
    if m=="---":raise ValueError("hole")
    y=int(m[0]);q=ord(m[2])-65
    if m[1]=="L":return C(q,lt,prepend(c.r,(y,0,1)))
    b,rt=pop(c.r);return C(q,prepend(lt,(b,0,1),(y,0,1)),rt)

def sweep(p,q,bit,a,side):
    z=q;ws=[]
    for _ in range(a):
        m=p[2*z+bit]
        if m=="---" or m[1]!=side:return None
        ws.append(int(m[0]));z=ord(m[2])-65
    if z!=q or len(set(ws))!=1:return None
    return ws[0]

def macro(p,c,rec):
    s,r,q,period,turn,base=rec
    if c.q==q and c.l and c.l[0][0]==0 and c.l[0][2]>0 and c.r and c.r[0][0]==1:
        x,a,b=c.r[0]
        if a and a%s==0 and b>=r:
            j=(b-r)//s;k=a//s
            tail=subrun(c.r,a,s*j+r)
            if tail and tail[0][2]>0:
                bit,rt=pop(tail);_,lt=pop(c.l)
                d=C(0,prepend(lt,(bit,0,1),(1,a,s*j+r),(0,0,1)),rt)
                return "fill",d,(k,j,bit,lt,rt)
            elif not tail:
                _,lt=pop(c.l);d=C(0,prepend(lt,(0,0,1),(1,a,s*j+r),(0,0,1)),())
                return "fillBlank",d,(k,j,0,lt,())
    if c.l and (a:=c.l[0][1]):
        x,_,b=c.l[0];y=sweep(p,c.q,x,a,"L")
        if y is not None:
            lt=subrun(c.l,a,0);d=C(c.q,lt,prepend(c.r,(y,a,0)))
            return "left",d,(a,x,y,lt,c.r)
    if c.r and (a:=c.r[0][1]):
        x,_,b=c.r[0]
        try:bit,lt=pop(c.l)
        except ValueError:bit=-1
        if bit==x:
            y=sweep(p,c.q,x,a,"R")
            if y is not None:
                rt=subrun(c.r,a,0);d=C(c.q,prepend(lt,(bit,0,1),(y,a,0)),rt)
                return "right",d,(a,bit,x,y,lt,rt)
    return None

def path(p,st,tg,rec,limit=1000):
    c=st;hist=[];seen=set()
    for _ in range(limit):
        if c==tg:return hist
        if c in seen:return None
        seen.add(c);m=macro(p,c,rec)
        if m:typ,d,info=m
        else:
            try:d=primitive(p,c)
            except ValueError:return None
            typ,info="step",()
        hist.append((typ,c,d,info));c=d
    return None

def num(a,b):
    if a==0:return str(b)
    return f"({a}*n+{b})"

def bits(x):return "true" if x else "false"
def W(w):
    return "([] : List Bool)" if not w else "(List.replicate "+num(w[0][1],w[0][2])+" "+bits(w[0][0])+" ++ "+W(w[1:])+")"
def cfg(c):return f"⟨{c.q},{W(c.l)},{W(c.r)}⟩"
def table(p):
    a=["def table : PartialMachine := fun s =>","  match s.1.val,s.2 with"]
    for i,m in enumerate(p):
        if m!="---":a.append(f'  | {i//2},{bits(i%2)} => some (some ⟨{bits(m[0]=="1")},{bits(m[1]=="R")},{ord(m[2])-65}⟩)')
    a.append("  | _,_ => none");return "\n".join(a)

def solve_eq(raw,canonical):
    assert norm(raw)==canonical,(raw,canonical)
    if raw==canonical:return "by rfl"
    eqs=[]
    for _,g in groupby(raw,key=lambda x:x[0]):
        group=list(g)
        if len(group)>1:
            parts=[num(a,b) for x,a,b in group];expr=parts[-1]
            for part in reversed(parts[:-1]):expr=f"({part}+{expr})"
            canon=num(sum(a for x,a,b in group),sum(b for x,a,b in group))
            if expr!=canon:eqs.append(f"show {expr}={canon} by omega")
    return "by simp only [merge,List.replicate_append_replicate,List.append_nil]"+(" <;> simp only ["+",".join(eqs)+"]" if eqs else "")

def equalities(q,l,r,target,tag):
    assert target.q==q and target.l==norm(l) and target.r==norm(r)
    return f"""  have {tag}L : {W(l)} = {W(target.l)} := {solve_eq(l,target.l)}
  have {tag}R : {W(r)} = {W(target.r)} := {solve_eq(r,target.r)}"""

def emit(idx,tablecode,rec,ans):
    t,st,tg,hist=ans;s,r,q,period,turn,base=rec
    out=[f"namespace M{idx}",f"-- {tablecode}",table(parse(tablecode)),f"def family (n : Nat) : Z0 := {cfg(st)}",f"theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl",
    f"""theorem hbase (b : Bool) (L R : List Bool) : run0 table {base} (Q {q} (false::L) (U {r}++b::R)) = some (A (b::(U {r}++false::L)) R) := by rfl

theorem hentry (L R : List Bool) : run0 table {r+1} (A (U {r+1}++L) R) = some (Q {q} L (U {r}++false::R)) := by rfl

theorem hloop (L R : List Bool) : run0 table {s} (Q {q} (U {s}++L) R) = some (Q {q} L (U {s}++R)) := by rfl

theorem hturn (b : Bool) (L R : List Bool) : run0 table {turn} (A (false::L) (U {s-1}++b::R)) = some (A (b::(U {s}++L)) R) := by rfl

abbrev FCost := T {s} {r} {base} {turn}
theorem hfill (n : Nat) (b : Bool) (L R : List Bool) : run0 table (FCost n) (Q {q} (false::L) (U ({s}*n+{r})++b::R)) = some (A (b::(U ({s}*n+{r})++false::L)) R) :=
  fill table {q} {s} {r} {base} {turn} (by decide) hbase (clearA table {q} {s} {r} hentry hloop) hturn n b L R"""]
    seg=[];j=0
    while j<len(hist):
        typ,c,d,info=hist[j]
        if typ=="step":
            k=j+1
            while k<len(hist) and hist[k][0]=="step":k+=1
            seg.append(("fixed",c,hist[k-1][2],k-j));j=k
        else:seg.append(hist[j]);j+=1
    costs=[]
    for j,(typ,c,d,info) in enumerate(seg):
        name=f"phase{j}"
        if typ=="fixed":
            cost=str(info);pr="by rfl"
        elif typ in ("fill","fillBlank"):
            k,b,bit,L,R=info;m=num(k,b);cost=f"FCost {m}";length=(1,s*k,s*b+r)
            l0=((0,0,1),*L);r0=(length,(bit,0,1),*R);l1=((bit,0,1),length,(0,0,1),*L);r1=R
            if typ=="fillBlank":
                r0=(length,);h=f"hfillBlank {m} {W(L)}"
                if not any("theorem hfillBlank" in x for x in out):
                    out.append(f"""theorem hbaseBlank (L : List Bool) : run0 table {base} (Q {q} (false::L) (U {r})) = some (A (false::(U {r}++false::L)) []) := by rfl

theorem hturnBlank (L : List Bool) : run0 table {turn} (A (false::L) (U {s-1})) = some (A (false::(U {s}++L)) []) := by rfl

theorem hfillBlank (n : Nat) (L : List Bool) : run0 table (FCost n) (Q {q} (false::L) (U ({s}*n+{r}))) = some (A (false::(U ({s}*n+{r})++false::L)) []) :=
  fillBlank table {q} {s} {r} {base} {turn} (by decide) hbase hbaseBlank (clearA table {q} {s} {r} hentry hloop) hturn hturnBlank n L""")
            else:h=f"hfill {m} {bits(bit)} {W(L)} {W(R)}"
            pr=f"""by
  have H := {h}
  rw [show {s}*{m}+{r}={num(s*k,s*b+r)} by omega] at H
  change run0 table ({cost}) ⟨{c.q},{W(l0)},{W(r0)}⟩ = some ⟨0,{W(l1)},{W(r1)}⟩ at H
{equalities(c.q,l0,r0,c,'src')}
{equalities(d.q,l1,r1,d,'dst')}
  rw [srcL,srcR,dstL,dstR] at H
  exact H"""
            if typ=="fillBlank":
                pr=pr.replace(W(r0),f"U {num(s*k,s*b+r)}",1).replace("rw [srcL,srcR,dstL,dstR] at H\n  exact H","rw [srcL,dstL,dstR] at H\n  simpa only [List.append_nil] using H")
        elif typ in ("left","right"):
            if typ=="left":
                a,x,y,L,R=info;cost=f"{a}*n";l0=((x,a,0),*L);r0=R;l1=L;r1=((y,a,0),*R)
                out.append(f"theorem local{j} (L R : List Bool) : run0 table {a} (Q {c.q} (List.replicate {a} {bits(x)}++L) R) = some (Q {c.q} L (List.replicate {a} {bits(y)}++R)) := by rfl")
                h=f"manyL table {c.q} {a} {bits(x)} {bits(y)} local{j} n {W(L)} {W(R)}"
            else:
                a,bit,x,y,L,R=info;cost=f"{a}*n";l0=((bit,0,1),*L);r0=((x,a,0),*R);l1=((bit,0,1),(y,a,0),*L);r1=R
                out.append(f"theorem local{j} (L R : List Bool) : run0 table {a} (Q {c.q} ({bits(bit)}::L) (List.replicate {a} {bits(x)}++R)) = some (Q {c.q} ({bits(bit)}::(List.replicate {a} {bits(y)}++L)) R) := by rfl")
                h=f"manyR table {c.q} {a} {bits(bit)} {bits(x)} {bits(y)} local{j} n {W(L)} {W(R)}"
            pr=f"""by
  have H := {h}
  change run0 table ({cost}) ⟨{c.q},{W(l0)},{W(r0)}⟩ = some ⟨{d.q},{W(l1)},{W(r1)}⟩ at H
{equalities(c.q,l0,r0,c,'src')}
{equalities(d.q,l1,r1,d,'dst')}
  rw [srcL,srcR,dstL,dstR] at H
  exact H"""
        else:raise ValueError(typ)
        costs.append(cost)
        out.append(f"theorem {name} (n : Nat) : run0 table ({cost}) {cfg(c)} = some {cfg(d)} := {pr}")
    join="(phase0 n)"
    for j in range(1,len(seg)):join=f"(join0 {join} (phase{j} n))"
    out.append(f"def cost (n : Nat) : Nat := "+" + ".join(f"({c})" for c in costs))
    a,b=next((a,b) for x,a,b in (*st.l,*st.r) if a)
    out.append(f"""theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := {join}
  unfold cost family
  rw [show {a}*(n+1)+{b}={a}*n+{b+a} by omega]
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {t} cost entry (by intro n; unfold cost; omega) growth m hm
#print axioms never
end M{idx}""")
    return "\n\n".join(out)

def main(child):
    ns="BB6.Agent1Raw60"+child+"RecFill"
    parts=["import RecursiveFill","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false","set_option linter.unusedSimpArgs false",f"namespace {ns}","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1RecursiveFill"]
    cases=json.loads((ROOT/"recursive-families.json").read_text())[child]
    for idx,code,rec,t,q,pre,a,b,suf in cases:
        st=C(q,word("0"*pre)+((1,a,b),)+word(suf),())
        tg=C(q,word("0"*pre)+((1,a,b+a),)+word(suf),())
        hist=path(parse(code),st,tg,rec)
        assert hist is not None,idx
        parts.append(emit(idx,code,rec,(t,st,tg,hist)))
    parts.append("end "+ns)
    (ROOT/("Raw60"+child+"RecFill.lean")).write_text("\n\n".join(parts)+"\n",encoding="utf-8")

if __name__=="__main__":
    import sys
    main(sys.argv[1])
