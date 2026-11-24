"""Untrusted symbolic search; emits kernel-checked finite phases and sweep proofs.

Each repeat carries its own parameter (n or k); S marks an arbitrary untouched
tail.  No symbolic search result is used as a theorem without Lean checking
every fixed transition, sweep induction, and word equality.
"""
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
import multi
from generate_sweeps import parse
from collections import Counter

def clean(parts):
    out=[]
    for w,t in parts:
        if not w: continue
        if not t and out and not out[-1][1]: out[-1]=(out[-1][0]+w,None)
        else: out.append((w,t))
    return tuple(out)
def lit(w): return ((w,None),) if w else ()
def repeat(w,t): return ((w,t),)
def prefix(w): return w[0][0] if w and not w[0][1] else ''
def rest(w): return w[1:] if prefix(w) else w
def head(w):
    if not w:return '0'
    if w[0][1]:raise ValueError("opaque head")
    return w[0][0][0]
def tail(w):
    if not w:return ()
    if w[0][1]:raise ValueError("opaque tail")
    return clean(lit(w[0][0][1:])+w[1:])
def normalization(w):
    hist=[];w=clean(w)
    while True:
        for i in range(1,len(w)):
            p,pr=w[i-1];b,br=w[i]
            if not pr and br and br!="S" and p[-1]==b[-1]:
                ch=p[-1];pre=clean(w[:i-1]+lit(p[:-1]));suf=w[i+1:]
                v=clean(pre+repeat(ch+b[:-1],br)+lit(ch)+suf)
                hist.append((w,v,pre,suf,b[:-1],ch,br));w=v;break
        else:return w,hist
@dataclass(frozen=True)
class C:
    q:int
    l:tuple
    r:tuple
    def norm(self):return self.q,normalization(self.l)[0],normalization(self.r)[0]
def cfg(q,l,r):return C(q,clean(l),clean(r))
def step(p,c):
    a=p[2*c.q+int(head(c.l))]
    if a=='---':raise ValueError("hole")
    q,w=ord(a[2])-65,a[0]
    if a[1]=='R':return cfg(q,lit(head(c.r))+lit(w)+tail(c.l),tail(c.r))
    return cfg(q,tail(c.l),lit(w)+c.r)
local=lru_cache(maxsize=200000)(multi.local)
def pump(p,start,target,limit=500):
    c=start;hist=[];seen=set()
    for _ in range(limit):
        if c.norm()==target.norm():return hist,c
        if c in seen:return None
        seen.add(c);ok=False
        for sd in ['L','R']:
            w,o=(c.l,c.r) if sd=='L' else (c.r,c.l)
            lp=prefix(w);wr=rest(w);op=prefix(o)
            if not wr:continue
            I,tag=wr[0]
            if tag=="S":continue
            for j in range(min(20,len(op))+1):
                ans=local(p,c.q,lp if sd=='L' else op[:j],op[:j] if sd=='L' else lp,sd,I)
                if not ans:continue
                k,O=ans;w2=clean(lit(lp)+wr[1:]);o2=clean(lit(op[:j])+repeat(O,tag)+lit(op[j:])+rest(o))
                d=cfg(c.q,w2,o2) if sd=='L' else cfg(c.q,o2,w2)
                hist.append(('loop',c,d,k,sd,I,O,j,tag));c=d;ok=True;break
            if ok:break
        if ok:continue
        try:d=step(p,c)
        except ValueError:return None
        hist.append(('step',c,d,1));c=d
    return None

def bits(s):
    assert set(s)<=set("01")
    return "["+",".join("true" if c=="1" else "false" for c in s)+"]"
def app(*parts):return " ++ ".join("("+x+")" for x in parts if x!="[]") or "[]"
def word(w):return app(*["S" if t=="S" else (f"rep {bits(s)} {t}" if t else bits(s)) for s,t in w])
def lc(c):return f"⟨{c.q},{word(c.l)},{word(c.r)}⟩"
def cf(q,l,r):return f"⟨{q},{l},{r}⟩"
SIMP="List.append_assoc,List.cons_append,List.nil_append,List.append_nil"
def wordeq(name,a,b,args):
    lhs=word(a) if a else "([] : List Bool)"
    ls=[f"theorem {name} {args} : {lhs} = {word(b)} := by"]
    if a==b:return "\n".join(ls+["  rfl"])
    x,xs=normalization(a);y,ys=normalization(b)
    assert x==y,(x,y)
    while xs and ys and xs[-1]==ys[-1]:xs.pop();ys.pop()
    ls.append("  calc")
    for _,v,pre,suf,k,z,tag in xs:
        ls.append(f"    _ = {word(v)} := by simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=='1').lower()} {tag}")
    for v,_,pre,suf,k,z,tag in reversed(ys):
        ls.append(f"    _ = {word(v)} := by symm; simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=='1').lower()} {tag}")
    return "\n".join(ls)
def table(p):
    ls=["def table : PartialMachine := fun s =>","  match s.1.val,s.2 with"]
    for k,v in enumerate(p):
        if v!="---":
            ls.append(f"  | {k//2},{str(k%2==1).lower()} => some (some ⟨{str(v[0]=='1').lower()},{str(v[1]=='R').lower()},{ord(v[2])-65}⟩)")
    ls.append("  | _,_ => none")
    return "\n".join(ls)
def segments(hist):
    seg=[];i=0
    while i<len(hist):
        x=hist[i]
        if x[0]=='step':
            j=i+1
            while j<len(hist) and hist[j][0]=='step':j+=1
            seg.append(('fixed',x[1],hist[j-1][2],j-i));i=j
        else:seg.append(x);i+=1
    return seg
def macro(p,name,st,tg,params,expected):
    ans=pump(p,st,tg)
    assert ans is not None,(name,p)
    hist,last=ans
    args=" ".join(f"({x} : {'List Bool' if x=='S' else 'Nat'})" for x in params)
    arg=" ".join(params);ls=[];cost=[];tot=Counter()
    seg=segments(hist)
    for j,x in enumerate(seg):
        typ,c,d,k=x[:4]
        if typ=="fixed":
            ls.append(f"theorem {name}Phase{j} {args} : run0 table {k} {lc(c)} = some {lc(d)} := by rfl")
            cost.append(str(k));tot["fixed"]+=k;continue
        _,_,_,k,side,I,O,cut,tag=x
        if side=="L":
            lp,rp=prefix(c.l),prefix(c.r)[:cut]
            L,R=rest(c.l)[1:],clean(lit(prefix(c.r)[cut:])+rest(c.r))
            src=cf(c.q,app(bits(lp),bits(I),"L"),app(bits(rp),"R"))
            dst=cf(c.q,app(bits(lp),"L"),app(bits(rp),bits(O),"R"))
        else:
            lp,rp=prefix(c.l)[:cut],prefix(c.r)
            L,R=clean(lit(prefix(c.l)[cut:])+rest(c.l)),rest(c.r)[1:]
            src=cf(c.q,app(bits(lp),"L"),app(bits(rp),bits(I),"R"))
            dst=cf(c.q,app(bits(lp),bits(O),"L"),app(bits(rp),"R"))
        ls.append(f"theorem {name}Local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl")
        ls.append(f"theorem {name}Phase{j} {args} : run0 table ({k}*{tag}) {lc(c)} = some {lc(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} {name}Local{j} {tag} ({word(L)}) ({word(R)})")
        cost.append(f"{k}*{tag}");tot[tag]+=k
    for side,a,b in [('L',last.l,tg.l),('R',last.r,tg.r)]:
        if a!=b:ls.append(wordeq(name+"Final"+side,a,b,args))
    a,b,c=tot["fixed"],tot["n"],tot["k"]
    assert (a,b,c)==expected,(name,(a,b,c),expected)
    cst=f"{a}+{b}*n"+(f"+{c}*k" if "k" in params else "")
    ls.append(f"theorem {name} {args} : run0 table ({cst}) {lc(st)} = some {lc(tg)} := by")
    join=f"({name}Phase0 {arg})"
    for j in range(1,len(seg)):join=f"(join0 {join} ({name}Phase{j} {arg}))"
    ls.append(f"  have H := {join}")
    for side,a,b in [('L',last.l,tg.l),('R',last.r,tg.r)]:
        if a!=b:ls.append(f"  rw [{name}Final{side} {arg}] at H")
    ls.append(f"  rw [show {'+'.join(cost)} = {cst} by omega] at H")
    ls.append("  exact H")
    return "\n\n".join(ls),cst

TABLES={
98:"1RB0LB_1RC1LA_0RD0LA_1LD1RE_0RF0LB_---0RC",
99:"1RB0LB_1RC1LA_0RD0LC_1LD1RE_0RF0LB_---0RC",
102:"1RB0LB_1RC1LA_0RD1LB_1LD1RE_0RF0LB_---0RC",
103:"1RB0LB_1RC1LA_0RD1LD_1LD1RE_0RF0LB_---0RC",
100:"1RB0LB_1RC1LA_0RD0RC_1LD1RE_0RF0LB_---0RC",
101:"1RB0LB_1RC1LA_0RD0RF_1LD1RE_0RF0LB_---0RC",
205:"1RB0LB_1RC1LA_0RD0RC_1LD1RE_1RF0LB_---1LC",
104:"1RB0LB_1RC1LA_0RD1LE_1LD1RE_0RF0LB_---0RC",
679:"1RB1RC_1RC1LA_0RD1LE_1LD1RE_0RF0LB_---0RC"}
Z=repeat("0001","n");O=repeat("0101","n");S=repeat("X","S")
suffix=lit("01")
out=["import Agent48CounterCore","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false","namespace BB6.Agent10Recursive","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter"]
for i,s in TABLES.items():
    p=tuple(parse(s));out.extend([f"namespace R63M{i}","-- "+s,table(p)])
    if i==98:
        P=lit("000010101")
        def f(w):return cfg(3,P+w,())
        a=46
        out.append(macro(p,"increment",f(O+lit("0001")+S),f(Z+lit("0101")+S),("n","S"),(46,12,0))[0])
        out.append(macro(p,"finish",f(O+suffix),f(Z+lit("0001")+suffix),("n",),(44,12,0))[0])
        pf=bits("000010101")
        out.append(f"""
def family (n : Nat) : Z0 := ⟨3,{pf} ++ rep ZB n ++ [false,true],[]⟩
theorem entry : run0 table 47 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem incrementCanonical (n : Nat) (S : List Bool) :
    run0 table (46+12*n) ⟨3,{pf}++rep OB n++ZB++S,[]⟩ =
      some ⟨3,{pf}++rep ZB n++OB++S,[]⟩ := by
  exact increment n S
theorem growth (n : Nat) : run0 table (normCost 46 n + (44+12*n)) (family n) =
    some (family (n+1)) := by
  have h1 := normalize table 3 {pf} [] 46 incrementCanonical n [false,true]
  have h2 : run0 table (44+12*n) ⟨3,{pf}++rep OB n++[false,true],[]⟩ =
      some (family (n+1)) := by
    unfold family
    rw [rep_right ZB n]
    simpa only [ZB,OB,List.append_assoc,List.cons_append,List.nil_append] using finish n
  exact join0 h1 h2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 47 (fun n => normCost 46 n + (44+12*n))
    entry (by intro n; omega) growth m hm
""")
    elif i in (99,102,103):
        a=14 if i==103 else 16
        def f(w):return cfg(0,w,lit("10111"))
        out.append(macro(p,"increment",f(O+lit("0001")+S),f(Z+lit("0101")+S),("n","S"),(a,12,0))[0])
        out.append(macro(p,"finish",f(O+suffix),f(lit("0101")+Z+suffix),("n",),(32,12,0))[0])
        rf=bits("10111")
        out.append(f"""
def family (n : Nat) : Z0 := ⟨0,rep OB n ++ [false,true],{rf}⟩
theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem incrementCanonical (n : Nat) (S : List Bool) :
    run0 table ({a}+12*n) ⟨0,[]++rep OB n++ZB++S,{rf}⟩ =
      some ⟨0,[]++rep ZB n++OB++S,{rf}⟩ := by
  exact increment n S
theorem growth (n : Nat) : run0 table ((32+12*n)+initCost {a} n) (family n) =
    some (family (n+1)) := by
  have h1 : run0 table (32+12*n) (family n) =
      some ⟨0,OB++rep ZB n++[false,true],{rf}⟩ := by
    exact finish n
  have h2 := normalizeInit table 0 [] {rf} {a} incrementCanonical n [false,true]
  exact join0 h1 h2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 22 (fun n => (32+12*n)+initCost {a} n)
    entry (by intro n; omega) growth m hm
""")
    else:
        P4=lit("0000")+repeat("00","k")+lit("1")
        P6=lit("000000")+repeat("00","k")+lit("1")
        def d(w):return cfg(3,w,())
        incs={100:(18,12,4),101:(18,12,4),205:(20,14,4),104:(22,12,8),679:(24,16,8)}
        fins={101:(32,12,4),205:(36,14,4),104:(32,12,8),679:(38,16,8)}
        code,ic=macro(p,"increment",d(P4+O+lit("0001")+S),d(P6+Z+lit("0101")+S),("k","n","S"),incs[i])
        out.append(code)
        if i==100:
            code,c0=macro(p,"finishZero",d(lit("00001")+O+suffix),d(lit("000010101")+Z+suffix),("n",),(32,12,0))
            out.append(code)
            code,cs=macro(p,"finishSucc",d(P6+O+suffix),d(P6+lit("0101")+Z+suffix),("k","n"),(36,12,4))
            out.append(code)
            fproof=f"""  cases k with
  | zero =>
    refine ⟨{c0},by omega,?_⟩
    simpa only [padFrame,pad,ZB,OB,rep,{SIMP}] using finishZero n
  | succ k =>
    refine ⟨{cs},by omega,?_⟩
    simpa only [padFrame,pad,ZB,OB,rep,{SIMP}] using finishSucc k n"""
        else:
            code,fc=macro(p,"finish",d(P4+O+suffix),d(P4+lit("0101")+Z+suffix),("k","n"),fins[i])
            out.append(code)
            fproof=f"""  refine ⟨{fc},by omega,?_⟩
  simpa only [padFrame,pad,ZB,OB,rep,{SIMP}] using finish k n"""
        entry=17 if i in (205,679) else 15
        out.append(f"""
theorem incrementReach (k n : Nat) (S : List Bool) :
    Reaches table (padFrame k (rep OB n ++ ZB ++ S))
      (padFrame (k+1) (rep ZB n ++ OB ++ S)) := by
  refine ⟨{ic},?_⟩
  simpa only [padFrame,pad,ZB,OB,rep,{SIMP}] using increment k n S
theorem finishReach (k n : Nat) :
    PosReach table (padFrame k (rep OB n ++ [false,true]))
      (padFrame k (OB ++ rep ZB n ++ [false,true])) := by
{fproof}
theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (padFrame 0 [false,true]) := by rfl
theorem initial : PadInvariant (padFrame 0 [false,true]) := ⟨0,0,rfl⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table PadInvariant {entry} _ entry initial
    (padProgress table incrementReach finishReach) m hm
""")
    out.extend(["#print axioms never",f"end R63M{i}"])
out.append("end BB6.Agent10Recursive")
(ROOT/"Agent48Raw63Counter.lean").write_text("\n\n".join(out)+"\n")
