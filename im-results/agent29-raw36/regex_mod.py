"""Modulo-preserving widening variants for parity-sensitive sweeps."""
import regex_search as r,json,sys,time
from functools import lru_cache
from concurrent.futures import ProcessPoolExecutor

@lru_cache(maxsize=200000)
def widen(p,threshold,retain,maxword,mod=2,skip=''):
 out=[]
 for w,s in p:
  if s:out.append((w,s));continue
  k=0;last=0
  while k<len(w):
   best=None
   for m in range(1,min(maxword,(len(w)-k)//threshold)+1):
    block=w[k:k+m]
    if skip and len(set(block))==1 and block[0] in skip:continue
    n=1
    while w.startswith(block,k+n*m):n+=1
    if n>=threshold and n-retain>=mod and (best is None or n*m>best[0]*best[1]):best=(m,n,block)
   if best is None:k+=1;continue
   m,n,b=best
   if k>last:out.append((w[last:k],False))
   out.extend([(b*(retain+(n-retain)%mod),False),(b*mod,True)])
   k+=m*n;last=k
  if last<len(w):out.append((w[last:],False))
 return r.normalize(tuple(out))

def task(row):
 i,t=row.split()
 for mod,th,ret,mw,skip in [(2,4,2,12,''),(2,6,3,12,''),(3,6,2,12,''),(4,7,3,12,''),(1,4,2,12,'0'),(1,4,2,12,'1'),(1,4,2,12,'01'),(2,6,2,12,'0'),(2,6,2,12,'1'),(2,8,4,16,'')]:
  r.widen=lambda p,threshold,retain,maxword:widen(p,threshold,retain,maxword,mod,skip)
  x,last=r.solve(t,th,ret,mw,limit=12000,timeout=5)
  if x:return [i,t,th,ret,mw,x,last+[mod,skip] if isinstance(last,list) else list(last)+[mod,skip]]
 return [i,t,None,None,None,None,last]
if __name__=='__main__':
 with ProcessPoolExecutor(max_workers=2) as ex:
  for v in ex.map(task,[x for x in open(sys.argv[1]) if x.strip()]):print(json.dumps(v),flush=True)
