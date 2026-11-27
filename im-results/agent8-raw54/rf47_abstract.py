"""Discover RF47's finite macro invariant (untrusted generator).

Run python rf47_abstract.py 4 7 4 200000 Raw54E1RF47Data.lean.
The Lean source independently verifies every abstract successor.
"""
from collections import defaultdict,deque
import sys
T=int(sys.argv[1]) if len(sys.argv)>1 else 4
P=int(sys.argv[2]) if len(sys.argv)>2 else 7
K=int(sys.argv[3]) if len(sys.argv)>3 else 4
LIMIT=int(sys.argv[4]) if len(sys.argv)>4 else 200000
C=lambda n:n if n<T else T+(n-T)%P
def add(a,b):return C(a+b)
def sub(a,d):return [x for x in range(T+P) if C(x+d)==a]
E=[defaultdict(set),defaultdict(set)]
wait=[defaultdict(set),defaultdict(set)]
seen=set();todo=deque();queued=set();src={};current=None

def queue(c):
 if c not in queued:queued.add(c);todo.append(c)
def config(l,r):
 c=l,r
 if c not in seen:
  seen.add(c);src[c]=current;queue(c)
def push(d,a,s):
 t=(a,)+s[:K-1]
 if s not in E[d][t]:
  E[d][t].add(s)
  for c in wait[d][t]:queue(c)
 return t
def pop(d,s):
 if not s:return ()
 wait[d][s].add(current)
 return tuple(E[d][s])
def right_prepend_zeros(r,z):
 if not r:return [()]
 g,b=r[0];return [push(1,(add(g,z),b),rr) for rr in pop(1,r)]
def right_prepend_run(r,n):
 return [push(1,(0,n),rr) for rr in right_prepend_zeros(r,1)]
def advance(l,r):
 if not l or l[0]!=0:
  if l and l[0]==1:return 'left gap=1'
  ls=[()] if not l else [push(0,x,lr) for x in sub(l[0],1) for lr in pop(0,l)]
  rs=[(0,r)]
  if r and r[0][0]==0:rs=[(r[0][1],rr) for rr in pop(1,r)]
  for b,rr in rs:
   if not rr:
    for ll in ls:config(push(0,0,ll),push(1,(0,add(b,2)),()))
   else:
    g,c=rr[0]
    if g==0 or c==0:return 'invalid right run'
    if g==1:
     for rt in pop(1,rr):
      for cc in sub(c,1):
       rout=rt if cc==0 else push(1,(0,cc),rt)
       for ll in ls:config(push(0,b,push(0,1,ll)),rout)
    else:
     for rt in pop(1,rr):
      for gg in sub(g,2):
       if gg==0:rout=push(1,(0,add(add(b,2),c)),rt)
       else:rout=push(1,(0,add(b,2)),push(1,(gg,c),rt))
       for ll in ls:config(push(0,0,ll),rout)
 else:
  for ll in pop(0,l):
   if not ll:
    for rr in right_prepend_run(r,3):config((),rr)
    continue
   g=ll[0]
   if g==0:return 'adjacent ones'
   for lt in pop(0,ll):
    if g==1:
     if not lt:out=[push(0,0,())]
     else:out=[push(0,0,push(0,add(lt[0],1),tail)) for tail in pop(0,lt)]
     for lout in out:
      for rr in right_prepend_zeros(r,1):config(lout,rr)
    elif g==2:
     if lt and lt[0]==0:return 'gap2 followed by adjacent ones'
     for rr in right_prepend_run(r,2):config(push(0,0,lt),rr)
    else:
     for gg in sub(g,3):
      for rr in right_prepend_run(r,3):config(push(0,gg,lt),rr)
 return None

r=push(1,(1,1),());r=push(1,(0,3),r);config((),r)
steps=0
while todo:
 current=todo.popleft();queued.remove(current);steps+=1
 why=advance(*current)
 if why:
  print('FAIL',T,P,K,why,'steps',steps,'seen',len(seen),'bad',current)
  path=[];c=current
  while c is not None and len(path)<30:path.append(c);c=src[c]
  for c in reversed(path):print(c)
  raise SystemExit(1)
 if len(seen)>LIMIT:raise SystemExit('LIMIT')
else:
 print('PASS',T,P,K,steps,len(seen),[len(e) for e in E])
 if len(sys.argv)>5:
  assert (T,P,K)==(4,7,4), "The checked Lean semantics is specific to this quotient."
  from pathlib import Path
  def term(x):
   if isinstance(x,int):return str(x)
   if isinstance(x,tuple):return '('+','.join(term(v) for v in x)+')'
   return '['+','.join(term(v) for v in x)+']'
  def state(s):return [*s]
  def edge(e):return (state(e[0]),state(e[1]))
  le=sorted((s,t) for s,ts in E[0].items() for t in ts)
  re=sorted((s,t) for s,ts in E[1].items() for t in ts)
  conf=[(state(l),state(r)) for l,r in sorted(seen)]
  print('edges',len(le),len(re))
  assert (len(le),len(re),len(conf))==(46,395,428)
  chunks=[conf[i:i+8] for i in range(0,len(conf),8)]
  path=Path(sys.argv[5]);path.write_text('import Raw54E1RF47Sound\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent8Raw54.RF47\n'
    +'def leftEdges : EL := '+term([edge(e) for e in le])+'\n'
    +'def rightEdges : ER := '+term([edge(e) for e in re])+'\n'
    +'\n'.join(f'def chunk{i} : List (ML × MR) := '+str(c) for i,c in enumerate(chunks))+'\n'
    +'def states : List (ML × MR) := '+' ++ '.join(f'chunk{i}' for i in range(len(chunks)))+'\n'
    +'end BB6.Agent8Raw54.RF47\n',encoding='utf-8')
