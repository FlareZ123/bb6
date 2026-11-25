"""Untrusted multi-block affine sweep discovery; generated Lean proofs are authoritative."""
from dataclasses import dataclass
from functools import lru_cache
from collections import defaultdict
import generate_sweeps as pump

@dataclass(frozen=True)
class Rep:
    word: str

def compact(xs):
    out=[]
    for x in xs:
        if not x: continue
        if isinstance(x,str) and out and isinstance(out[-1],str): out[-1]+=x
        else: out.append(x)
    return tuple(out)

@dataclass(frozen=True)
class Word:
    parts: tuple=()
    @staticmethod
    def of(*parts): return Word(compact(parts))
    def head(self):
        if not self.parts: return '0'
        if isinstance(self.parts[0],Rep): raise ValueError('opaque')
        return self.parts[0][0]
    def tail(self):
        if not self.parts: return self
        if isinstance(self.parts[0],Rep): raise ValueError('opaque')
        return Word.of(self.parts[0][1:],*self.parts[1:])
    def cons(self,b): return Word.of(b,*self.parts)
    def prefix(self): return self.parts[0] if self.parts and isinstance(self.parts[0],str) else ''
    def split(self,i):
        p=self.prefix()
        assert 0<=i<=len(p)
        return p[:i],Word.of(p[i:],*self.parts[int(bool(p)):])
    def firstrep(self):
        p=self.prefix()
        i=int(bool(p))
        if len(self.parts)>i and isinstance(self.parts[i],Rep):
            return p,self.parts[i].word,Word.of(*self.parts[i+1:])
    def normalize(self):
        w=self
        steps=[]
        while True:
            found=False
            for i,x in enumerate(w.parts):
                if not isinstance(x,Rep) or i==0 or not isinstance(w.parts[i-1],str): continue
                b=w.parts[i-1][-1]
                if b!=x.word[-1]: continue
                pre=Word.of(*w.parts[:i-1],w.parts[i-1][:-1])
                suf=Word.of(*w.parts[i+1:])
                p=x.word[:-1]
                new=Word.of(*pre.parts,Rep(b+p),b,*suf.parts)
                steps.append((w,new,pre,suf,b,p))
                w=new
                found=True
                break
            if not found: return w,steps
    def normal(self): return self.normalize()[0]
    def inc(self): return Word.of(*(y for x in self.parts for y in ((x.word,x) if isinstance(x,Rep) else (x,))))

@dataclass(frozen=True)
class Config:
    q:int
    l:Word
    r:Word
    def normal(self): return self.q,self.l.normal(),self.r.normal()

def step(p,c):
    a=p[2*c.q+int(c.l.head())]
    if a=='---': raise ValueError('hole')
    q,w=ord(a[2])-65,a[0]
    if a[1]=='R': return Config(q,c.l.tail().cons(w).cons(c.r.head()),c.r.tail())
    return Config(q,c.l.tail(),c.r.cons(w))

def loops(p,c):
    for side,w,other in [('L',c.l,c.r),('R',c.r,c.l)]:
        a=w.firstrep()
        if a is None: continue
        pre,block,tail=a
        for j in range(min(len(other.prefix()),16)+1):
            op,ot=other.split(j)
            m=pump.local(p,c.q,pre if side=='L' else op,op if side=='L' else pre,side,block)
            if not m: continue
            k,out=m
            v=Word.of(pre,*tail.parts)
            u=Word.of(op,Rep(out),*ot.parts)
            d=Config(c.q,v,u) if side=='L' else Config(c.q,u,v)
            yield ('loop',c,d,k,side,block,out,pre,op,tail,ot)
            break

def execute(p,start,target,limit=500):
    c=start
    hist=[]
    seen=set()
    goal=target.normal()
    for i in range(limit):
        if c.normal()==goal: return hist,c
        if c in seen: return None
        seen.add(c)
        options=list(loops(p,c))
        if options:
            x=options[0]
            hist.append(x)
            c=x[2]
            continue
        try: d=step(p,c)
        except ValueError: return None
        hist.append(('step',c,d,1))
        c=d
    return None

def infer(a,b,c,maxrep=3,maxlen=16):
    if not (0<len(b)-len(a)<=maxlen and len(c)-len(b)==len(b)-len(a)): return
    @lru_cache(None)
    def paths(i,j,k,r):
        if i==len(a) and j==len(b) and k==len(c): return ((),)
        out=[]
        if i<len(a) and j<len(b) and k<len(c) and a[i]==b[j]==c[k]:
            for rest in paths(i+1,j+1,k+1,r): out.append((a[i],)+rest)
        if r:
            for d in range(1,min(len(b)-j,(len(c)-k)//2,maxlen)+1):
                block=b[j:j+d]
                if c[k:k+2*d]!=block*2: continue
                for rest in paths(i,j+d,k+2*d,r-1): out.append((Rep(block),)+rest)
        return tuple(out[:256])
    seen=set()
    for parts in paths(0,0,0,maxrep):
        w=Word.of(*parts)
        if w not in seen:
            seen.add(w)
            yield w

def discover(p,limit=5000):
    ev=pump.concrete_events(p,limit)
    groups=defaultdict(list)
    for t,s,c in ev:
        if (s=='L' and c.l.pre=='') or (s=='R' and c.r.pre==''):
            groups[s,c.q].append((t,c.r.pre if s=='L' else c.l.pre))
    attempted=set()
    for (side,q),g in groups.items():
        for i,(t,a) in enumerate(g[:60]):
            for j in range(i+1,min(i+9,len(g))):
                _,b=g[j]
                diff=len(b)-len(a)
                if not 1<=diff<=16: continue
                for k in range(j+1,min(j+9,len(g))):
                    _,c=g[k]
                    if len(c)-len(b)!=diff: continue
                    for w in infer(a,b,c):
                        if sum(isinstance(x,Rep) for x in w.parts)<2: continue
                        v=w.inc()
                        start=Config(q,Word(),w) if side=='L' else Config(q,w,Word())
                        target=Config(q,Word(),v) if side=='L' else Config(q,v,Word())
                        if (start,target) in attempted: continue
                        attempted.add((start,target))
                        res=execute(p,start,target)
                        if res: return t,start,target,res
    return None

SIMP=pump.SIMP
bits=pump.bits
app=pump.app
def word(w,n='n'):
    return app(*(f'rep {bits(x.word)} ({n})' if isinstance(x,Rep) else bits(x) for x in w.parts))
def cfg(c,n='n'): return '⟨'+str(c.q)+','+word(c.l,n)+','+word(c.r,n)+'⟩'
def context(q,l,r): return '⟨'+str(q)+','+l+','+r+'⟩'

def equal_word(name,a,b):
    lhs=word(a) if a.parts else '([] : List Bool)'
    lines=[f'theorem {name} (n : Nat) : {lhs} = {word(b)} := by']
    if a==b: return '\n'.join(lines+['  rfl'])
    x,s=a.normalize()
    y,t=b.normalize()
    assert x==y
    while s and t and s[-1]==t[-1]:
        s.pop()
        t.pop()
    lines.append('  calc')
    for _,v,pre,suf,z,p in s:
        lines.append(f"    _ = {word(v)} := by simpa only [{SIMP}] using congrArg (fun w : List Bool => {app(word(pre),'w',word(suf))}) (rotate {str(z=='1').lower()} {bits(p)} n)")
    for v,_,pre,suf,z,p in reversed(t):
        lines.append(f"    _ = {word(v)} := by symm; simpa only [{SIMP}] using congrArg (fun w : List Bool => {app(word(pre),'w',word(suf))}) (rotate {str(z=='1').lower()} {bits(p)} n)")
    return '\n'.join(lines)

def generate(idx,p,ans):
    t,st,target,(hist,last)=ans
    ls=[f'namespace M{idx}',pump.tab(p),f'def family (n : Nat) : Z0 := {cfg(st)}',
        f'theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl']
    seg=[]
    i=0
    while i<len(hist):
        x=hist[i]
        if x[0]=='step':
            j=i+1
            while j<len(hist) and hist[j][0]=='step': j+=1
            seg.append(('fixed',x[1],hist[j-1][2],j-i))
            i=j
        else:
            seg.append(x)
            i+=1
    costs=[]
    for j,x in enumerate(seg):
        typ,c,d,k=x[:4]
        if typ=='fixed':
            ls.append(f'theorem phase{j} (n : Nat) : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl')
            costs.append(str(k))
            continue
        _,_,_,k,side,I,O,pre,op,tail,ot=x
        if side=='L':
            lp,rp=pre,op
            L,R=tail,ot
            src=context(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'))
            dst=context(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
        else:
            lp,rp=op,pre
            L,R=ot,tail
            src=context(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'))
            dst=context(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
        ls.append(f'theorem local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
        ls.append(f'theorem phase{j} (n : Nat) : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} local{j} n ({word(L)}) ({word(R)})')
        costs.append(f'{k}*n')
    ls.extend((equal_word('finalL',last.l,target.l),equal_word('finalR',last.r,target.r)))
    a=sum(x[3] for x in seg if x[0]=='fixed')
    b=sum(x[3] for x in seg if x[0]=='loop')
    proof=f'theorem growth (n : Nat) : run0 table ({a}+{b}*n) (family n) = some (family (n+1)) := by\n'
    join='(phase0 n)'
    for j in range(1,len(seg)): join=f'(join0 {join} (phase{j} n))'
    proof+=f'  have H := {join}\n'
    for name,w,v in [('finalL',last.l,target.l),('finalR',last.r,target.r)]:
        if w!=v: proof+=f'  rw [{name} n] at H\n'
    proof+=f"  rw [show {'+'.join(costs)}={a}+{b}*n by omega] at H\n  simpa only [family,rep,{SIMP}] using H"
    ls.append(proof)
    ls.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {t} (fun n => {a}+{b}*n) entry (by intro n; omega) growth m hm')
    ls.append('#print axioms never')
    ls.append(f'end M{idx}')
    return '\n\n'.join(ls),(t,a,b)
