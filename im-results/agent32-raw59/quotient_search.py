"""Find deterministic stack-automaton quotients of sparse n-gram witnesses."""
from collections import defaultdict,deque
from pathlib import Path
import sys,json

def parse(line):
 _,l,r,n,L,R,S=line.split();l,r,n=map(int,(l,r,n));M=1<<(l+r)
 def edges(s):return [(int(x),b) for x,v in (a.split(':') for a in s.rstrip(',').split(',')) for b in (0,1) if int(v)&(1<<b)]
 E=[edges(L),edges(R)];W=[l,r];C=[{0},{0}];profiles=[defaultdict(set),defaultdict(set)];states=[];push=[{},{}]
 for i in map(int,S.rstrip(',').split(',')):
  s,v=divmod(i,M);x,y=divmod(v,1<<r);states.append((s,x,y));C[0].add(x);C[1].add(y);profiles[0][x].add((s,y));profiles[1][y].add((s,x))
 for d in range(2):
  for x,b in E[d]:
   y=x//2+(b<<(W[d]-1));a=x%2;C[d].update((x,y));assert push[d].get((y,a),x)==x;push[d][y,a]=x
 assert len(states)==n
 return C,profiles,push,states

def partition(C,key):
 keys={};c={}
 for x in sorted(C):
  k=key(x)
  if k not in keys:keys[k]=len(keys)
  c[x]=keys[k]
 return c

def refine(C,push,c):
 while True:
  new=partition(C,lambda x:(c[x],tuple(c.get(push.get((x,b)),-1) for b in (0,1))))
  if new==c:return c
  c=new

def dfa(C,push,c):
 sz=max(c.values())+1;delta=[None]*(2*sz)
 for x,k in c.items():
  for b in (0,1):
   dest=c.get(push.get((x,b)),-1);i=2*k+b
   assert delta[i] is None or delta[i]==dest
   delta[i]=dest
 return [max(0,x) for x in delta]

def witness(table,D,cap=200000):
 T=table.replace('_','');T=[T[3*i:3*i+3] for i in range(12)]
 Es=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)];Seen={(0,0,0)};todo=deque(Seen)
 for e in Es:e[0].add((0,0))
 def add(s,l,r):
  x=(s,l,r)
  if x not in Seen:Seen.add(x);todo.append(x)
 def pop(st,b,src):
  s,l,r=st;w,d,q=T[s];w=int(w);q=ord(q)-65
  if d=='R':add(q*2+b,D[0][2*l+w],src)
  else:add(q*2+b,src,D[1][2*r+w])
 while todo:
  if len(Seen)>cap:return None,len(Seen),'cap'
  st=todo.popleft();s,l,r=st;w,d,q=T[s]
  if w=='-':return None,len(Seen),'hole'
  w=int(w);d=int(d=='R');src=l if d else r;dest=D[1-d][2*src+w];e=(w,src)
  if e not in Es[1-d][dest]:
   Es[1-d][dest].add(e)
   for v in wait[1-d][dest]:pop(v,*e)
  x=r if d else l;wait[d][x].append(st)
  for b,y in Es[d][x]:pop(st,b,y)
 return Es,len(Seen),Seen

def search(line,table,verbose=True):
 C,P,push,states=parse(line); candidates=[]
 def try_c(cl,label):
  D=[dfa(C[d],push[d],cl[d]) for d in range(2)];Es,n,info=witness(table,D)
  if verbose:print(label,'classes',len(D[0])//2,len(D[1])//2,'states',n,'pass' if Es is not None else info,flush=True)
  if Es is not None:
   e=sum(len(v) for e in Es for v in e.values());candidates.append((n,e,label,D))
  return Es is not None
 cl=[refine(C[d],push[d],partition(C[d],lambda x:0)) for d in range(2)];try_c(cl,'language')
 cl=[refine(C[d],push[d],partition(C[d],lambda x:frozenset(s for s,_ in P[d][x]))) for d in range(2)];try_c(cl,'slots')
 for it in range(8):
  new=[refine(C[d],push[d],partition(C[d],lambda x:(cl[d][x],frozenset((s,cl[1-d][y]) for s,y in P[d][x])))) for d in range(2)]
  if new==cl:break
  cl=new
  if try_c(cl,f'partner {it+1}'):break
 cl=[refine(C[d],push[d],partition(C[d],lambda x:frozenset(P[d][x]))) for d in range(2)];assert try_c(cl,'exact profiles')
 n,e,label,D=min(candidates);return {'table':table,'dfa':D,'states':n,'edges':e,'method':label}
