from collections import Counter
import sys,time
D=211

def node(s):
    x,y=s; p=(x+y)%2; q=x+y-D*p
    if x<=0 or y<=0 or q<=0:return None
    v=(q&-q).bit_length()-1
    req=(212*(x+y+1688)).bit_length()
    if y%2 and (x+y)%4 in (1,2):return (req,())
    out=[]
    if y%2==0:out.append((1,(x+y+2*D,(y+2*D)//2)))
    for n in range((x+1+p)%2,v-1,2):
        a=q//(1<<(n+1))+D*(2+p)
        k=x+2*y+D*(7+3*n)-a
        assert k%2==0
        out.append((n+2,(a,k//2)))
    return (max(req,v+1),tuple(out))

def root(w):
    z=1360+22155*w
    return 44*z+D,42*z+D

def check(w, limit=1_000_000):
    budget=201+3360*w
    work=[(root(w),0,0)]; steps=0; required=0; depth=0
    while work:
        s,spent,d=work.pop(); steps+=1; depth=max(depth,d)
        if steps>limit:return False,required,depth,steps,'limit'
        r=node(s)
        if r is None:return False,required,depth,steps,'invalid'
        req,ch=r; required=max(required,req+spent)
        if required>budget:return False,required,depth,steps,'budget'
        work.extend((p,spent+delta,d+1) for delta,p in ch)
    return True,required,depth,steps,'ok'

if __name__=='__main__':
    start=time.monotonic(); counts=Counter(); fail=[]; maxr=maxd=maxsteps=0
    N=int(sys.argv[1]) if len(sys.argv)>1 else 10000
    limit=int(sys.argv[2]) if len(sys.argv)>2 else 1000000
    for w in range(N):
        ok,req,dep,steps,reason=check(w,limit)
        if ok: counts[w%8]+=1; maxr=max(maxr,req); maxd=max(maxd,dep); maxsteps=max(maxsteps,steps)
        else: fail.append((w,req,dep,steps,reason)); print('FAIL',fail[-1],flush=True)
        if w%1000==999:print(w+1,sum(counts.values()),len(fail),'max',maxr,maxd,maxsteps,'elapsed',round(time.monotonic()-start,2),flush=True)
    print('final',counts,fail)
