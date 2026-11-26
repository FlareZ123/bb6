"""Untrusted inference of four universally quantified binary-counter macros.
Every accepted witness must pass Agent46CounterCheck in Lean."""
import itertools, json, sys, time
from collections import defaultdict
from autoword import C, Word, step, symstep, sweeps

def packword(w):
    return [w.pre,w.block,packword(w.post)] if w.block else w.pre

def nextbits(bs, ext):
    i=bs.find('0')
    return '0'*len(bs)+ext if i<0 else '0'*i+'1'+bs[i+1:]

def packpath(path):
    ops=[]
    for info in path:
        if info is None:
            if ops and isinstance(ops[-1],int): ops[-1]+=1
            else: ops.append(1)
        else:
            dr,lp,rp,I,O,k,L,R=info
            if dr=='L': lp,rp,L,R=rp,lp,R,L
            ops.append([dr,lp,rp,I,O,packword(L),packword(R),k])
    return ops

def symbolic_to(t,f,g,openR,deadline=float('inf'),maxsteps=180,maxsweeps=12):
    target=g.norm(); seen=set()
    def dfs(z,path,cost,sweepcount):
        if z.norm()==target and path: return dict(ops=packpath(path),a=cost[0],b=cost[1])
        if time.monotonic()>deadline or len(path)>=maxsteps or sweepcount>maxsweeps or z in seen: return None
        seen.add(z)
        for y,info in sweeps(t,z):
            if y==z: continue
            r=dfs(y,path+[info],(cost[0]+info[5],cost[1]),sweepcount+1)
            if r: return r
        try:
            if openR and not z.r.pre and not z.r.block:
                if t[3*(2*z.q+int(z.l.head()))+1]=='R': return None
            y=symstep(t,z)
        except ValueError: return None
        if y.l.size()+y.r.size()>400: return None
        return dfs(y,path+[None],(cost[0],cost[1]+1),sweepcount)
    return dfs(f,[],(0,0),0)

def prove_shape(t,q,l,pre,d0,d1,post,ext,entry,seed,budget=1):
    encode=lambda bs: ''.join(d1 if b=='1' else d0 for b in bs)
    w=lambda r: C(q,Word(l),r if isinstance(r,Word) else Word(r))
    goals=[(w(pre+d0),w(pre+d1),True),
           (w(Word(pre+d1,d1,d0)),w(Word(pre+d0,d0,d1)),True),
           (w(pre+post),w(pre+encode(ext)+post),False),
           (w(Word(pre+d1,d1,post)),w(Word(pre+d0,d0,encode(ext)+post)),False)]
    deadline=time.monotonic()+budget; ms=[]
    for f,g,o in goals:
        r=symbolic_to(t,f,g,o,deadline)
        if not r:return None
        ms.append(r)
    return dict(table=t,shape=[q,l,pre,d0,d1,post,ext],entry=entry,seed=seed,macros=ms)

def candidates(a,b):
    # Infer common literal boundaries and a two-symbol block alphabet from a
    # pair of equal-size frames. Increment must change a nonempty prefix only.
    if len(a)!=len(b) or a==b:return
    size=len(a)
    for w in range(1,min(7,size//2+1)):
        for pre in range(min(5,size-1)+1):
            for post in range(min(6,size-pre-1)+1):
                if (size-pre-post)%w:continue
                if a[:pre]!=b[:pre] or (post and a[-post:]!=b[-post:]):continue
                x=[a[i:i+w] for i in range(pre,size-post,w)]
                y=[b[i:i+w] for i in range(pre,size-post,w)]
                ds=sorted(set(x+y))
                if len(ds)!=2:continue
                for d0,d1 in itertools.permutations(ds):
                    bs=''.join('1' if s==d1 else '0' for s in x)
                    cs=''.join('1' if s==d1 else '0' for s in y)
                    if nextbits(bs,'1')==cs:
                        yield a[:pre],d0,d1,a[size-post:],bs

def infer_counter(t,budget=3,limit=15000):
    deadline=time.monotonic()+budget; z=(0,'',''); hist=defaultdict(list); tried=set()
    for j in range(limit):
        if time.monotonic()>deadline:return None
        q,l,r=z
        if len(l)<=12 and 2<=len(r)<=150:
            h=hist[q,l]
            for i,a in reversed(h[-4:]):
                for pre,d0,d1,post,bs in candidates(a,r):
                    for ext in ('1','0','01','10'):
                        key=(q,l,pre,d0,d1,post,ext)
                        if key in tried:continue
                        tried.add(key)
                        if time.monotonic()>deadline:return None
                        f=prove_shape(t,*key,i,bs,budget=min(.3,deadline-time.monotonic()))
                        if f:return f
            if not h or h[-1][1]!=r:h.append((j,r))
        z=step(t,z)
        if z is None:return None
    return None

if __name__=='__main__':
    tables=[x.strip() for x in open(sys.argv[1]) if x.strip()]
    out=[]
    budget=float(sys.argv[3]) if len(sys.argv)>3 else 3
    for t in tables:
        f=infer_counter(t,budget)
        print(t,'FOUND' if f else 'FAIL',flush=True)
        if f:out.append(f)
    with open(sys.argv[2],'w') as file:
        json.dump(out,file,indent=2)
