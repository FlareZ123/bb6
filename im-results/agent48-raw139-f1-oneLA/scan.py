from collections import Counter
from itertools import product
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
def scan(p,limit=250):
 q=h=x=0; off=limit+1; hist=[]
 for t in range(limit+1):
  lo=hi=h
  for i in range(t-1,-1,-1):
   a,b,z=hist[i];lo=min(lo,b);hi=max(hi,b)
   if a!=q:continue
   d=h-b
   if d>=0 and z>>(lo+off)==x>>(lo+off+d):return ('cycle',i,t-i,True,lo)
   if d<=0 and z&((1<<(hi+off+1))-1)==(x&((1<<(hi+off+d+1))-1))<<(-d):return ('cycle',i,t-i,False,hi)
  s=2*q+((x>>(h+off))&1);v=p[s]
  if v==24:return ('hole',t,s)
  hist.append((q,h,x)); bit=1<<(h+off)
  x=(x&~bit)|(((v>>1)&1)<<(h+off));h+=1 if v&1 else -1;q=v>>2
 return ('open',)
def far(p,rev,D):
 d=len(D)//2;N=6*d+1;h=1<<(N-1);T=[0]*(2*N);rules=[];T[N-1]=T[-1]=h
 for b,l,q in product(range(2),range(d),range(6)):
  a=p[2*q+b]; dst=b*N+6*l+q
  if a==24:T[dst]=h;continue
  n=a>>2;w=(a>>1)&1;r=a&1
  if r!=rev:T[dst]=1<<(6*D[2*l+w]+n)
  else:
   for j,x in product(range(d),range(2)):
    if D[2*j+x]==l:rules.append((dst,x*N+6*j+n,w*N))
 while True:
  changed=False
  for dst,src,off in rules:
   v=T[src];nw=T[dst]
   while v:
    bit=v&-v;v-=bit;nw|=T[off+bit.bit_length()-1]
   if nw!=T[dst]:T[dst]=nw;changed=True
  if not changed:break
 z=h
 while True:
  old=z
  for i in range(N):
   if T[i]&z:z|=1<<i
  if old==z:break
 if z&1:return None
 return (rev,d,list(D),T[:N],T[N:],z)
def find_far(p,maxd=2):
 for d in range(1,maxd+1):
  for tail in product(range(d),repeat=2*d-1):
   D=(0,)+tail
   for rev in [0,1]:
    c=far(p,rev,D)
    if c:return c
 return None
def tree(p,counts,opens,limit,maxd):
 a=scan(p,limit)
 if a[0]=='cycle':counts['cycle']+=1;return a
 if a[0]=='hole':
  _,n,s=a
  counts['maxquery']=max(counts['maxquery'],n)
  if p.count(24)==1:counts['last']+=1;return ('last',n,s)
  counts['split']+=1;return ('split',n,s,[tree(p[:s]+[v]+p[s+1:],counts,opens,limit,maxd) for v in ORDER])
 c=find_far(p,maxd)
 if c:counts['far']+=1;return ('far',*c)
 counts['open']+=1;opens.append(p);return ('open',p)
