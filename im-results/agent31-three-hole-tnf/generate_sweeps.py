#!/usr/bin/env python3
"""Untrusted discovery + Lean proof-term generator for one-parameter sweep families.

No finite simulation result is accepted as a theorem. Opaque-word execution
only proposes finite rfl equations; the generated Lean file checks all of
them, universally quantifies the untouched tails and uses sweep induction.
"""
from dataclasses import dataclass
from pathlib import Path
import argparse

TABLES = [
    "1RB0RB_1RC1LF_0RD0LF_1LD1RE_---0LB_0RF0LA",
    "1RB---_1RC1LF_0RD0RC_1LD1RE_1LB0LB_1LE0LA",
    "1RB1RF_1RC1LF_0RD0RF_1LD1RE_---0LB_0RE0LA",
    "1RB---_1RC1LF_0RD1LC_1LD1RE_0RE0LB_0RF0LA",
    "1RB0RF_1RC1LF_0RD1RA_1LD1RE_---0LB_1LA0LA",
    "1RB1LE_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA",
    "1RB1LF_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA",
    "1RB1RD_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA",
    "1RB1LA_1RC1LF_0RD1RC_1LD1RE_1RB0LB_---0LA",
    # F1=0RA sibling E0-open leaf: candidate for a symbolic counter/sweep proof.
    "1RB0LB_1RC1LF_0RD0LA_1LD1RE_---0LB_0RC0RA",
    # F1=0RA sibling C1-open leaf with A1=0LB, E0=1RF, F0=0LB.
    "1RB0LB_1RC1LF_0RD---_1LD1RE_1RF0LB_0LB0RA",
]

def parse(s):
    s = s.replace("_", "")
    assert len(s) == 36
    return tuple(s[i:i+3] for i in range(0, 36, 3))

def show(p):
    return "_".join("".join(p[i:i+2]) for i in range(0, 12, 2))

@dataclass(frozen=True)
class W:
    pre: str = ""
    block: str = ""
    suf: str = ""

    def head(self):
        if self.pre:
            return self.pre[0]
        if self.block:
            raise ValueError("opaque head")
        return "0"

    def tail(self):
        if self.pre:
            return W(self.pre[1:], self.block, self.suf)
        if self.block:
            raise ValueError("opaque tail")
        return self

    def cons(self, b):
        return W(b + self.pre, self.block, self.suf)

    def normal(self):
        if not self.block:
            return self.pre + self.suf, "", ""
        p, b, s = self.pre, self.block, self.suf
        while p and p[-1] == b[-1]:
            a = p[-1]
            p, b, s = p[:-1], a+b[:-1], a+s
        return p,b,s

@dataclass(frozen=True)
class C:
    q: int
    h0: int
    hn: int
    l: W
    r: W

    def norm(self):
        return self.q,self.h0,self.hn,self.l.normal(),self.r.normal()

def step(p,c):
    a = p[2*c.q + int(c.l.head())]
    if a == "---":
        raise ValueError("hole")
    q,w = ord(a[2])-65,a[0]
    if a[1] == "R":
        return C(q,c.h0+1,c.hn,c.l.tail().cons(w).cons(c.r.head()),c.r.tail())
    return C(q,c.h0-1,c.hn,c.l.tail(),c.r.cons(w))

def local(p,q,l,r,side,block,limit=100):
    # X and Y are arbitrary untouched list tails; no inspection is allowed.
    c=C(q,0,0,W(l+(block if side=="L" else ""),"X",""),W(r+(block if side=="R" else ""),"Y",""))
    for i in range(1,limit+1):
        try:
            c=step(p,c)
        except ValueError:
            return None
        if c.q!=q:
            continue
        if side=="L" and c.h0==-len(block) and c.l.pre==l and c.r.pre.startswith(r) and len(c.r.pre)==len(r)+len(block):
            return i,c.r.pre[len(r):]
        if side=="R" and c.h0==len(block) and c.r.pre==r and c.l.pre.startswith(l) and len(c.l.pre)==len(l)+len(block):
            return i,c.l.pre[len(l):]
    return None

def pump(p,start,target,maxsteps=400):
    c=start
    history=[]
    seen=set()
    for _ in range(maxsteps):
        if c.norm()==target.norm():
            return history,c
        if c in seen:
            return None
        seen.add(c)
        side="L" if c.l.block else "R" if c.r.block else None
        if side:
            w=c.l if side=="L" else c.r
            other=c.r if side=="L" else c.l
            if not other.block:
                for j in range(min(len(other.pre),16)+1):
                    m=local(p,c.q,w.pre if side=="L" else other.pre[:j],
                        other.pre[:j] if side=="L" else w.pre,side,w.block)
                    if m:
                        break
                if m:
                    k,out=m
                    ow=W(other.pre[:j],out,other.pre[j:]+other.suf)
                    if side=="L":
                        d=C(c.q,c.h0,c.hn-len(w.block),W(w.pre+w.suf),ow)
                    else:
                        d=C(c.q,c.h0,c.hn+len(w.block),ow,W(w.pre+w.suf))
                    history.append(("loop",c,d,k,side,w.block,out,j))
                    c=d
                    continue
        try:
            d=step(p,c)
        except ValueError:
            return None
        history.append(("step",c,d,1))
        c=d
    return None

def concrete_events(p,limit=3000):
    c=C(0,0,0,W(),W())
    lo=hi=0
    ev=[]
    for t in range(limit):
        if c.h0<lo or c.h0>hi:
            side="L" if c.h0<lo else "R"
            lo,hi=min(lo,c.h0),max(hi,c.h0)
            ev.append((t,side,c))
        try:
            c=step(p,c)
        except ValueError:
            break
    return ev

def candidate(p,ev):
    for i,(t,s,c) in enumerate(ev[:60]):
        for j in range(i+1,min(i+12,len(ev))):
            _,s2,d=ev[j]
            if s!=s2 or c.q!=d.q:
                continue
            delta=d.h0-c.h0
            if s=="L" and c.l.pre==d.l.pre=="":
                a,b,side=c.r.pre,d.r.pre,"R"
            elif s=="R" and c.r.pre==d.r.pre=="":
                a,b,side=c.l.pre,d.l.pre,"L"
            else:
                continue
            diff=len(b)-len(a)
            if not 1<=diff<=16:
                continue
            for k in range(len(a)+1):
                if b[:k]!=a[:k] or b[k+diff:]!=a[k:]:
                    continue
                block=b[k:k+diff]
                pred=a[:k]+block*2+a[k:]
                if not any(e[1]==s and e[2].q==c.q and e[2].h0==c.h0+2*delta
                    and (e[2].r.pre if side=="R" else e[2].l.pre)==pred for e in ev[j+1:j+12]):
                    continue
                w,v=W(a[:k],block,a[k:]),W(a[:k]+block,block,a[k:])
                start=C(c.q,0,0,W() if side=="R" else w,w if side=="R" else W())
                target=C(c.q,delta,0,W() if side=="R" else v,v if side=="R" else W())
                res=pump(p,start,target)
                if res:
                    return t,c,start,target,res
    return None

def bits(s):
    return "["+",".join("true" if b=="1" else "false" for b in s)+"]"

def app(*xs):
    return " ++ ".join("("+x+")" for x in xs if x!="[]") or "[]"

def word(w,n="n"):
    if not w.block:
        return bits(w.pre+w.suf)
    return app(bits(w.pre),f"rep {bits(w.block)} ({n})",bits(w.suf))

def cfg(c,n="n"):
    return "⟨"+str(c.q)+","+word(c.l,n)+","+word(c.r,n)+"⟩"

def config(q,l,r):
    return "⟨"+str(q)+","+l+","+r+"⟩"

def tab(p):
    lines=["def table : PartialMachine := fun s =>","  match s.1.val,s.2 with"]
    for i,a in enumerate(p):
        if a!="---":
            lines.append(f"  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩)")
    lines.append("  | _,_ => none")
    return "\n".join(lines)

def cuts(w):
    out=[]
    p,b,s=w.pre,w.block,w.suf
    if not b:
        return out
    while p and p[-1]==b[-1]:
        x=p[-1]
        out.append((W(p,b,s),W(p[:-1],x+b[:-1],x+s),p[:-1],s,b[:-1],x))
        p,b,s=p[:-1],x+b[:-1],x+s
    return out

SIMP="List.append_assoc,List.cons_append,List.nil_append,List.append_nil"

def wordeq(name,a,b):
    lhs=word(a) if word(a)!="[]" else "([] : List Bool)"
    lines=[f"theorem {name} (n : Nat) : {lhs} = {word(b)} := by"]
    if a==b:
        lines.append("  rfl")
        return "\n".join(lines)
    x,y=cuts(a),cuts(b)
    assert a.normal()==b.normal()
    while x and y and x[-1]==y[-1]:
        x.pop()
        y.pop()
    lines.append("  calc")
    for _,v,p,s,k,z in x:
        lines.append(f"    _ = {word(v)} := by simpa only [{SIMP}] using moveCut {bits(p)} {bits(s)} {bits(k)} {str(z=='1').lower()} n")
    for v,_,p,s,k,z in reversed(y):
        lines.append(f"    _ = {word(v)} := by symm; simpa only [{SIMP}] using moveCut {bits(p)} {bits(s)} {bits(k)} {str(z=='1').lower()} n")
    return "\n".join(lines)

def generate(idx,p,ans):
    t,_,st,target,(hist,last)=ans
    ls=[f"namespace M{idx}",f"-- {show(p)}",tab(p),
        f"def family (n : Nat) : Z0 := {cfg(st)}",
        f"theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl"]
    seg=[]
    i=0
    while i<len(hist):
        x=hist[i]
        if x[0]=="step":
            j=i+1
            while j<len(hist) and hist[j][0]=="step":
                j+=1
            seg.append(("fixed",x[1],hist[j-1][2],j-i))
            i=j
        else:
            seg.append(x)
            i+=1
    costs=[]
    for j,x in enumerate(seg):
        typ,c,d,k=x[:4]
        if typ=="fixed":
            ls.append(f"theorem phase{j} (n : Nat) : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl")
            costs.append(str(k))
            continue
        _,_,_,k,side,I,O,cut=x
        if side=="L":
            lp,rp=c.l.pre,c.r.pre[:cut]
            L,R=c.l.suf,c.r.pre[cut:]+c.r.suf
            src=config(c.q,app(bits(lp),bits(I),"L"),app(bits(rp),"R"))
            dst=config(c.q,app(bits(lp),"L"),app(bits(rp),bits(O),"R"))
        else:
            lp,rp=c.l.pre[:cut],c.r.pre
            L,R=c.l.pre[cut:]+c.l.suf,c.r.suf
            src=config(c.q,app(bits(lp),"L"),app(bits(rp),bits(I),"R"))
            dst=config(c.q,app(bits(lp),bits(O),"L"),app(bits(rp),"R"))
        ls.append(f"theorem local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl")
        ls.append(f"theorem phase{j} (n : Nat) : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} local{j} n {bits(L)} {bits(R)}")
        costs.append(f"{k}*n")
    ls.extend((wordeq("finalL",last.l,target.l),wordeq("finalR",last.r,target.r)))
    a=sum(x[3] for x in seg if x[0]=="fixed")
    b=sum(x[3] for x in seg if x[0]=="loop")
    proof=f"theorem growth (n : Nat) : run0 table ({a}+{b}*n) (family n) = some (family (n+1)) := by\n"
    join="(phase0 n)"
    for j in range(1,len(seg)):
        join=f"(join0 {join} (phase{j} n))"
    proof+=f"  have H := {join}\n"
    for name,w,v in [("finalL",last.l,target.l),("finalR",last.r,target.r)]:
        if w!=v:
            proof+=f"  rw [{name} n] at H\n"
    proof+=f"  rw [show {'+'.join(costs)}={a}+{b}*n by omega] at H\n  simpa only [family,rep,{SIMP}] using H"
    ls.append(proof)
    ls.append(f"theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {t} (fun n => {a}+{b}*n) entry (by intro n; omega) growth m hm")
    ls.append("#print axioms never")
    ls.append(f"end M{idx}")
    return "\n\n".join(ls),(t,a,b)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,default=Path(__file__).with_name("SweepData.lean"))
    args=ap.parse_args()
    parts=["import SweepPumping","set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
        "namespace BB6Coverage.Agent31Pump","open BB6Coverage"]
    for i,s in enumerate(TABLES):
        p=parse(s)
        ans=candidate(p,concrete_events(p))
        if ans is None:
            raise RuntimeError(f"no inductive family for {s}")
        code,info=generate(i,p,ans)
        print(i,s,"entry, intercept, slope =",info)
        parts.append(code)
    parts.append("end BB6Coverage.Agent31Pump")
    args.output.write_text("\n\n".join(parts)+"\n",encoding="utf-8")

if __name__=="__main__":
    main()
