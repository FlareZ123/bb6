"""Discover symbolic one-parameter sweeps. The Lean generator checks all candidates."""
from dataclasses import dataclass

TABLE="1RB1LD1RC1LA1LA1RE1RF0LA1LB0RE---1RD"
def tab(s):
    return [None if s[i]=="-" else (int(s[i]),s[i+1]=="R",ord(s[i+2])-65) for i in range(0,36,3)]

@dataclass(frozen=True)
class W:
    pre:str=""
    block:str=""
    suf:str=""
    def value(self,k): return self.pre+self.block*k+self.suf
    def cons(self,x): return W(x+self.pre,self.block,self.suf)
    def pop(self):
        if self.pre: return self.pre[0],W(self.pre[1:],self.block,self.suf)
        if not self.block: return "0",self
        if self.suf.startswith(self.block):
            return self.block[0],W(self.block[1:],self.block,self.suf[len(self.block):])
        raise ValueError("variable head")
    def pull(self):
        pre,suf=self.pre,self.suf
        while self.block and pre.endswith(self.block):
            pre=pre[:-len(self.block)]
            suf=self.block+suf
        return W(pre,self.block,suf)

def primitive(tr,z):
    q,l,r=z
    b,l2=l.pop()
    ins=tr[2*q+int(b)]
    if ins is None: raise ValueError("hole")
    w,d,p=ins
    if d:
        c,r2=r.pop()
        return p,l2.cons(c+str(w)),r2
    return p,l2,r.cons(str(w))

def raw(tr,z):
    q,l,r=z
    b=(l or "0")[0]
    if b in "XY": return None
    ins=tr[2*q+int(b)]
    if ins is None: return None
    w,d,p=ins
    if d:
        c=(r or "0")[0]
        if c in "XY": return None
        return p,c+str(w)+l[1:],r[1:]
    return p,l[1:],str(w)+r

def detect(tr,z,maxsteps=1000,maxframe=48):
    q,l,r=z
    direction=bool(r.block)
    if not l.block and not r.block: return None
    inp,out=(r,l) if direction else (l,r)
    inp=inp.pull()
    rp,B=inp.pre,inp.block
    if len(rp)>maxframe: return None
    for j in range(min(maxframe,len(out.pre))+1):
        lp=out.pre[:j]
        cur=(q,lp+"Y",rp+B+"X") if direction else (q,rp+B+"X",lp+"Y")
        for t in range(1,maxsteps+1):
            cur=raw(tr,cur)
            if cur is None: break
            p,a,b=cur
            if not direction: a,b=b,a
            if p==q and b==rp+"X" and a.startswith(lp) and a.endswith("Y"):
                O=a[len(lp):-1]
                if not O: continue
                ni=W(rp+inp.suf)
                no=W(lp,O,out.pre[j:])
                nz=(q,no,ni) if direction else (q,ni,no)
                return (t,direction,rp,lp,B,O,inp,out),nz
    return None

def symrun(table,L,R,stop,limit=10000):
    tr=tab(table)
    z=(0,L,R)
    ops=[]
    for n in range(limit):
        if stop(z,n): return z,ops
        sweep=detect(tr,z)
        if sweep:
            meta,nz=sweep
            ops.append(("sweep",z,nz,meta))
        else:
            nz=primitive(tr,z)
            ops.append(("raw",z,nz))
        z=nz
    raise RuntimeError("symbolic search limit")
