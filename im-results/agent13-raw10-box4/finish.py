from collections import Counter
from math import prod
import itertools,json,time,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'agent13-raw10-box17'))
from lag_rle import run

def domain_for(target):
    fixed=[8,14,11,7,17,4]
    return tuple((fixed[i],) if i<6 else (0,) if i==target else tuple(v for v in range(1,25) if i!=6 or v!=9) for i in range(12))

def trace_long(t,limit=100000,cycle_limit=1000):
    L=R=q=h=0; seen={}; left={};right={};hist=[]
    for n in range(limit+1):
        s=2*q+(R&1);v=t[s]
        if v<=0:return ('hole' if v<0 else 'halt',n,s)
        if n<cycle_limit:
            key=(q,L,R)
            if key in seen:
                j=seen[key];dr=h>=hist[j]
                return ('cycle',j,n-j,dr,(min if dr else max)(hist[j:n]+[h]))
            seen[key]=n
            key=(q,R)
            old=right.get(key,[])
            for j,oh,oL in reversed(old):
                if h>oh:
                    lo=min(h,min(hist[j:n]))
                    if ((L^oL)&((1<<(oh-lo))-1))==0:return ('side',j,n-j,True,lo)
            right[key]=(old+[(n,h,L)])[-4:]
            key=(q,L)
            old=left.get(key,[])
            for j,oh,oR in reversed(old):
                if h<oh:
                    hi=max(h,max(hist[j:n]))
                    if ((R^oR)&((1<<(hi-oh+1))-1))==0:return ('side',j,n-j,False,hi)
            left[key]=(old+[(n,h,R)])[-4:]
            hist.append(h)
        if n==limit:return ('open',n,L.bit_length(),R.bit_length())
        v-=1;w=v//2%2
        if v%2:L=(L<<1)|w;R>>=1;h+=1
        else:R=(((R>>1)<<1)|w)<<1|(L&1);L>>=1;h-=1
        q=v//4

def run_target(target,chunk=0,batch=30):
 ds=domain_for(target);rows=[tuple(map(int,l.split())) for l in open(f'hard{target}.txt') if l.strip()];stack=rows[chunk*batch:(chunk+1)*batch];counts=Counter();mass=sum(prod(len(ds[i]) for i,v in enumerate(t) if v<0) for t in stack);out=[];fails=[];mx=(0,None);start=time.monotonic()
 opts=sorted(itertools.product(range(5),range(1,3),range(1,4),range(2,5)),key=lambda x:(x[1]+x[2])*x[3]+2*x[0])
 while stack:
  t=stack.pop();r=trace_long(t);typ=r[0]
  if typ=='hole':
   i=r[2];stack.extend(t[:i]+(v,)+t[i+1:] for v in ds[i]);continue
  if typ in ('halt','cycle','side'):
   if typ=='halt' and r[1]+1>mx[0]:mx=(r[1]+1,t)
   out.append([t,r]);counts[typ]+=1;continue
  for p in opts:
   c=run(t,(p,p),2500)
   if c is not None:out.append([t,['rle',p,len(c['states'])]]);counts['rle']+=1;break
  else:fails.append([t,r]);counts['hard']+=1
 assert sum(prod(len(ds[i]) for i,v in enumerate(t) if v<0) for t,_ in out+fails)==mass
 json.dump({'target':target,'chunk':chunk,'out':out,'fails':fails,'max':mx,'mass':mass,'counts':counts},open(f'long{target}-{chunk}.json','w'))
 print(target,chunk,counts,mx,'mass',mass,'seconds',round(time.monotonic()-start,2),flush=True)
if __name__=='__main__':run_target(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]) if len(sys.argv)>3 else 30)
