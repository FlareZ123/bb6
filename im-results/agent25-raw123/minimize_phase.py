"""Greedy congruence quotient; every successful merge rechecks sparse closure."""
from pathlib import Path
import sys,random,json
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"agent16-raw118"))
from bidfa_emit import witness

def quotient(d,edges,a,b):
 n=len(d)//2;par=list(range(n));pending=[(a,b)];out=[[-1,-1] for _ in range(n)]
 for dst,bit,src in edges:out[src][bit]=dst
 def find(x):
  while par[x]!=x:
   par[x]=par[par[x]];x=par[x]
  return x
 while pending:
  x,y=map(find,pending.pop())
  if x==y:continue
  if x>y:x,y=y,x
  par[y]=x
  for bit in (0,1):
   u,v=out[x][bit],out[y][bit]
   if u<0:out[x][bit]=v
   elif v>=0:pending.append((u,v))
 roots=sorted(set(map(find,range(n))));idx={x:i for i,x in enumerate(roots)}
 return [idx[find(out[x][b])] if out[x][b]>=0 else 0 for x in roots for b in (0,1)]

def minimize(p,dl,dr):
 d=[dl,dr];es,st=witness(p,*d);rng=random.Random(25)
 while True:
  changed=False
  for side in [0,1]:
   n=len(d[side])//2;pairs=[(i,j) for i in range(n) for j in range(i+1,n)];rng.shuffle(pairs)
   for i,j in pairs:
    c=quotient(d[side],es[side],i,j);z=d[:];z[side]=c
    try:e,s=witness(p,*z)
    except ValueError:continue
    if len(s)>max(2000,len(st)*2):continue
    d,es,st=z,e,s;changed=True;break
  if not changed:return [*d,len(st),sum(map(len,es))]

if __name__=='__main__':
 rows=dict(map(str.split,Path(sys.argv[1]).read_text().splitlines()));out={}
 for file in sys.argv[2:]:
  v=Path(file).read_text().split()
  if len(v)<9 or v[-1]=='NO':continue
  i=v[0];n,l,r=v[-3:];dl,dr=[[int(x) for x in s.split(':')[1].split(',') if x] for s in (l,r)]
  res=minimize(rows[i],dl,dr);out[i]=res
 print(json.dumps(out,separators=(',',':')))
