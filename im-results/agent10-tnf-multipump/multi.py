"""Multi-block symbolic extension of Agent31's one-block search.

Candidate discovery only. All emitted local transition equations and induction
steps are checked by Lean, with arbitrary untouched tails.
"""
from dataclasses import dataclass
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"agent31-three-hole-tnf"))
from generate_sweeps import parse,show,concrete_events,bits,app,tab,SIMP

# Part = (word, is_repeat), with every repeated word raised to the same n.
def clean(parts):
    out=[]
    for w,b in parts:
        if not w:continue
        if not b and out and not out[-1][1]:out[-1]=(out[-1][0]+w,False)
        else:out.append((w,b))
    return tuple(out)
def lit(w):return ((w,False),) if w else ()
def rep(w):return ((w,True),)
def prefix(w):return w[0][0] if w and not w[0][1] else ''
def rest(w):return w[1:] if prefix(w) else w
def head(w):
    if not w:return '0'
    if w[0][1]:raise ValueError('opaque head')
    return w[0][0][0]
def tail(w):
    if not w:return ()
    if w[0][1]:raise ValueError('opaque tail')
    return clean(lit(w[0][0][1:])+w[1:])
def cons(a,w):return clean(lit(a)+w)
def normalization(w):
    # Rotate a bit through a repeated word, preserving the literal list.
    # Each move is later justified by the existing Lean moveCut theorem.
    hist=[];w=clean(w)
    while True:
        for i in range(1,len(w)):
            p,pr=w[i-1];b,br=w[i]
            if not pr and br and p[-1]==b[-1]:
                ch=p[-1];pre=clean(w[:i-1]+lit(p[:-1]));suf=w[i+1:]
                v=clean(pre+rep(ch+b[:-1])+lit(ch)+suf)
                hist.append((w,v,pre,suf,b[:-1],ch));w=v;break
        else:return w,hist

@dataclass(frozen=True)
class C:
    q:int
    l:tuple
    r:tuple
    def norm(self):return self.q,normalization(self.l)[0],normalization(self.r)[0]

def step(p,c):
    a=p[2*c.q+int(head(c.l))]
    if a=='---':raise ValueError('hole')
    q,w=ord(a[2])-65,a[0]
    if a[1]=='R':return C(q,cons(head(c.r),cons(w,tail(c.l))),tail(c.r))
    return C(q,tail(c.l),cons(w,c.r))

def local(p,q,lp,rp,side,I,limit=100):
    # X and Y are distinct opaque arbitrary tails, never read.
    c=C(q,lit(lp+(I if side=='L' else ''))+rep('X'),lit(rp+(I if side=='R' else ''))+rep('Y'))
    for k in range(1,limit+1):
        try:c=step(p,c)
        except ValueError:return None
        if c.q!=q:continue
        l,r=prefix(c.l),prefix(c.r)
        if rest(c.l)!=rep('X') or rest(c.r)!=rep('Y'):continue
        if side=='L' and l==lp and r.startswith(rp) and len(r)==len(rp)+len(I):return k,r[len(rp):]
        if side=='R' and r==rp and l.startswith(lp) and len(l)==len(lp)+len(I):return k,l[len(lp):]
    return None

def pump(p,start,target,limit=500):
    # Greedy loop proposals, then fixed literal steps. Both tails may
    # already contain opaque repeated words; this is the key extension.
    c=start;hist=[];seen=set()
    for _ in range(limit):
        if c.norm()==target.norm():return hist,c
        if c in seen:return None
        seen.add(c);ok=False
        for sd in ['L','R']:
            w,o=(c.l,c.r) if sd=='L' else (c.r,c.l)
            lp=prefix(w);wr=rest(w);op=prefix(o)
            if not wr:continue
            I=wr[0][0]
            assert wr[0][1]
            for j in range(min(16,len(op))+1):
                ans=local(p,c.q,lp if sd=='L' else op[:j],op[:j] if sd=='L' else lp,sd,I)
                if not ans:continue
                k,O=ans;w2=clean(lit(lp)+wr[1:]);o2=clean(lit(op[:j])+rep(O)+lit(op[j:])+rest(o))
                d=C(c.q,w2,o2) if sd=='L' else C(c.q,o2,w2)
                hist.append(('loop',c,d,k,sd,I,O,j));c=d;ok=True;break
            if ok:break
        if ok:continue
        try:d=step(p,c)
        except ValueError:return None
        hist.append(('step',c,d,1));c=d
    return None

def candidates(p,ev):
    # Infer two simultaneous insertions from three concrete fresh-boundary
    # observations. These observations propose families, not proofs.
    for i,(t,side,c) in enumerate(ev[:55]):
        for j in range(i+1,min(i+14,len(ev))):
            _,s2,d=ev[j]
            if c.q!=d.q or side!=s2:continue
            delta=d.h0-c.h0
            if side=='L' and c.l.pre==d.l.pre=='':a,b=c.r.pre,d.r.pre;left=False
            elif side=='R' and c.r.pre==d.r.pre=='':a,b=c.l.pre,d.l.pre;left=True
            else:continue
            diff=len(b)-len(a)
            if not 2<=diff<=16:continue
            thirds={e[2].l.pre if left else e[2].r.pre for e in ev[j+1:j+14] if e[1]==side and e[2].q==c.q and e[2].h0==c.h0+2*delta}
            if not thirds:continue
            for k in range(len(a)+1):
                if a[:k]!=b[:k]:break
                for d1 in range(1,diff):
                    d2=diff-d1;I=b[k:k+d1]
                    for m in range(k,len(a)+1):
                        if b[k+d1:m+d1]!=a[k:m]:break
                        J=b[m+d1:m+diff]
                        if b[m+diff:]!=a[m:]:continue
                        if a[:k]+I*2+a[k:m]+J*2+a[m:] not in thirds:continue
                        w=clean(lit(a[:k])+rep(I)+lit(a[k:m])+rep(J)+lit(a[m:]))
                        v=clean(lit(a[:k]+I)+rep(I)+lit(a[k:m]+J)+rep(J)+lit(a[m:]))
                        st=C(c.q,w if left else (),() if left else w)
                        tg=C(c.q,v if left else (),() if left else v)
                        yield t,st,tg

def candidate(p,ev):
    for t,st,tg in candidates(p,ev):
        ans=pump(p,st,tg)
        if ans:return t,st,tg,ans
    return None

def word(w,n='n'):return app(*[f'rep {bits(s)} ({n})' if b else bits(s) for s,b in w])
def cfg(c,n='n'):return f'⟨{c.q},{word(c.l,n)},{word(c.r,n)}⟩'
def cf(q,l,r):return f'⟨{q},{l},{r}⟩'

def wordeq(name,a,b):
    lhs=word(a) if a else '([] : List Bool)'
    ls=[f'theorem {name} (n : Nat) : {lhs} = {word(b)} := by']
    if a==b:return '\n'.join(ls+['  rfl'])
    x,xs=normalization(a);y,ys=normalization(b);assert x==y
    while xs and ys and xs[-1]==ys[-1]:xs.pop();ys.pop()
    ls.append('  calc')
    for _,v,pre,suf,k,z in xs:
        ls.append(f'    _ = {word(v)} := by simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
    for v,_,pre,suf,k,z in reversed(ys):
        ls.append(f'    _ = {word(v)} := by symm; simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
    return '\n'.join(ls)

def generate(idx,p,ans,epoch=False):
    t,st,target,(hist,last)=ans
    ls=[f'namespace M{idx}',f'-- {show(p)}',tab(p)]
    if not epoch:
        ls.extend([f'def family (n : Nat) : Z0 := {cfg(st)}',f'theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl'])
    seg=[];i=0
    while i<len(hist):
        x=hist[i]
        if x[0]=='step':
            j=i+1
            while j<len(hist) and hist[j][0]=='step':j+=1
            seg.append(('fixed',x[1],hist[j-1][2],j-i));i=j
        else:seg.append(x);i+=1
    costs=[]
    for j,x in enumerate(seg):
        typ,c,d,k=x[:4]
        if typ=='fixed':
            ls.append(f'theorem phase{j} (n : Nat) : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl')
            costs.append(str(k));continue
        _,_,_,k,side,I,O,cut=x
        if side=='L':
            lp,rp=prefix(c.l),prefix(c.r)[:cut]
            L,R=rest(c.l)[1:],clean(lit(prefix(c.r)[cut:])+rest(c.r))
            src=cf(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'))
            dst=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
        else:
            lp,rp=prefix(c.l)[:cut],prefix(c.r)
            L,R=clean(lit(prefix(c.l)[cut:])+rest(c.l)),rest(c.r)[1:]
            src=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'))
            dst=cf(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
        ls.append(f'theorem local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
        ls.append(f'theorem phase{j} (n : Nat) : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} local{j} n ({word(L)}) ({word(R)})')
        costs.append(f'{k}*n')
    ls.extend((wordeq('finalL',last.l,target.l),wordeq('finalR',last.r,target.r)))
    a=sum(x[3] for x in seg if x[0]=='fixed')
    b=sum(x[3] for x in seg if x[0]=='loop')
    if epoch:
        proof=f'theorem epoch (n : Nat) : run0 table ({a}+{b}*n) {cfg(st)} = some {cfg(target)} := by\n'
    else:
        proof=f'theorem growth (n : Nat) : run0 table ({a}+{b}*n) (family n) = some (family (n+1)) := by\n'
    join='(phase0 n)'
    for j in range(1,len(seg)):join=f'(join0 {join} (phase{j} n))'
    proof+=f'  have H := {join}\n'
    for name,w,v in [('finalL',last.l,target.l),('finalR',last.r,target.r)]:
        if w!=v:proof+=f'  rw [{name} n] at H\n'
    proof+=f"  rw [show {'+'.join(costs)}={a}+{b}*n by omega] at H\n"
    proof+='  exact H' if epoch else f"  simpa only [family,rep,{SIMP}] using H"
    ls.append(proof)
    if not epoch:
        ls.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {t} (fun n => {a}+{b}*n) entry (by intro n; omega) growth m hm')
        ls.append('#print axioms never')
    ls.append(f'end M{idx}')
    return '\n\n'.join(ls),(t,a,b)


def long_candidate(p,ev,side,q,period,maxdiff=64):
    """Propose two insertions at a fixed same-state boundary-return period."""
    es=[(t,c) for t,s,c in ev if s==side and c.q==q
        and (not c.l.pre if side=='L' else not c.r.pre)]
    for i in range(min(40,len(es)-2*period)):
        t,c=es[i];_,d=es[i+period];_,e=es[i+2*period]
        a,b,z=[v.r.pre if side=='L' else v.l.pre for v in (c,d,e)]
        diff=len(b)-len(a)
        if not 2<=diff<=maxdiff or len(z)-len(b)!=diff:continue
        for k in range(len(a)+1):
            if a[:k]!=b[:k]:break
            for d1 in range(1,diff):
                I=b[k:k+d1]
                for j in range(k,len(a)+1):
                    if b[k+d1:j+d1]!=a[k:j]:break
                    J=b[j+d1:j+diff]
                    if b[j+diff:]!=a[j:] or a[:k]+I*2+a[k:j]+J*2+a[j:]!=z:continue
                    w=clean(lit(a[:k])+rep(I)+lit(a[k:j])+rep(J)+lit(a[j:]))
                    v=clean(lit(a[:k]+I)+rep(I)+lit(a[k:j]+J)+rep(J)+lit(a[j:]))
                    st=C(q,w if side=='R' else (),() if side=='R' else w)
                    tg=C(q,v if side=='R' else (),() if side=='R' else v)
                    ans=pump(p,st,tg,3000)
                    if ans:return t,st,tg,ans
    return None
