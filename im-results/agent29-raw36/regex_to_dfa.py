"""Compile ray-pattern membership to two finite word summaries.
The complete finite abstract successor relation is independently checked.
"""
import collections,json,sys,time

def compile_dfa(patterns,limit=20000):
 pats=list(dict.fromkeys(patterns));nfa=[];eps=[];ends=0;start=0
 def add():
  k=len(nfa);nfa.append({});eps.append([]);return k
 for p in pats:
  at=add();start|=1<<at
  for w,s in reversed(p):
   k=at
   for j,b in enumerate(reversed(w)):
    if s and j+1==len(w):nfa[at][int(b)]=k;at=add();eps[k].append(at)
    else:a=add();nfa[at][int(b)]=a;at=a
  ends|=1<<at
 C=[]
 for i in range(len(nfa)):
  v=1<<i;stack=[i]
  while stack:
   a=stack.pop()
   for b in eps[a]:
    if not v>>b&1:v|=1<<b;stack.append(b)
  C.append(v)
 def bits(v):
  while v:
   b=v&-v;v-=b;yield b.bit_length()-1
 T=[tuple(C[e[c]] if c in e else 0 for c in (0,1)) for e in nfa]
 init=0
 for x in bits(start):init|=C[x]
 ids={init:0};todo=[init];D=[];O=[]
 for s in todo:
  O.append(s&ends);ds=[0,0]
  for i in bits(s):
   a,b=T[i];ds[0]|=a;ds[1]|=b
  for j,x in enumerate(ds):
   if x not in ids:
    if len(ids)>=limit:raise RuntimeError('DFA limit')
    ids[x]=len(ids);todo.append(x)
   ds[j]=ids[x]
  D.append(tuple(ds))
 h={};cls=[h.setdefault(o,len(h)) for o in O]
 while True:
  h={};nc=[h.setdefault((cls[i],cls[a],cls[b]),len(h)) for i,(a,b) in enumerate(D)]
  if nc==cls:break
  cls=nc
 d=[None]*len(h)
 for i,(a,b) in enumerate(D):d[cls[i]]=(cls[a],cls[b])
 return d,len(nfa),len(D)

def inv(table,L,R):
 p=table.replace('_','');p=[p[i:i+3] for i in range(0,36,3)];LP=[[[] for _ in range(2)] for _ in L];RP=[[[] for _ in range(2)] for _ in R]
 for D,P in [(L,LP),(R,RP)]:
  for i,(a,b) in enumerate(D):P[a][0].append(i);P[b][1].append(i)
  P[0][0].append(0)
 init=(0,0,0);seen={init};todo=[init]
 for q,l,r in todo:
  for a in (0,1):
   if not LP[l][a]:continue
   tr=p[2*q+a]
   if tr=='---':return None
   w,d,nq=int(tr[0]),tr[1],ord(tr[2])-65
   for ll in LP[l][a]:
    if d=='L':xs=[(nq,ll,R[r][w])]
    else:xs=[(nq,L[L[ll][w]][b],rr) for b in (0,1) for rr in RP[r][b]]
    for z in xs:
     if z not in seen:seen.add(z);todo.append(z)
 return todo

def main():
 for row in map(json.loads,open(sys.argv[1])):
  if row[-2] is None:continue
  i,t,*_,cert,_=row
  L=list(dict.fromkeys(tuple((w,s) for w,s in l) for q,l,r in cert));R=list(dict.fromkeys(tuple((w,s) for w,s in r) for q,l,r in cert));now=time.monotonic()
  try:
   dl,nl,ol=compile_dfa(L);dr,nr,orr=compile_dfa(R);I=inv(t,dl,dr)
   print(json.dumps([i,t,dl,dr,I,[len(L),len(R),nl,nr,ol,orr,time.monotonic()-now]]),flush=True)
  except RuntimeError as e:print(json.dumps([i,t,None,None,None,[str(e)]]),flush=True)
if __name__=='__main__':main()
