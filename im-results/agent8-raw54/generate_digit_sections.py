"""Arbitrary-tail exact binary digit section proof emitter.
Search is untrusted; generated Lean checks all local computations and induction.
"""
from pathlib import Path
from collections import deque
from dataclasses import dataclass
import sys
@dataclass(frozen=True)
class C:
 q:int;l:str;r:str;p:str
 def concrete(self,n):return self.q,self.l.replace('V',self.p*n),self.r.replace('V',self.p*n)
class M:
 def __init__(self,s):self.a=[s.replace('_','')[j:j+3] for j in range(0,36,3)]
 def step(self,q,l,r):
  if l and l[0] not in '01':return
  w,d,k=self.a[2*q+int(l[0] if l else '0')]
  if w=='-':return
  q=ord(k)-65
  if d=='R':
   if r and r[0] not in '01':return
   return q,(r[0] if r else '0')+w+l[1:],r[1:]
  return q,l[1:],w+r

def sweep(M,c):
 left='V'in c.l;s,d=(c.l,c.r) if left else (c.r,c.l);pre,suf=s.split('V');p=c.p
 if any(a not in '01' for a in pre):return
 lim=next((i for i,a in enumerate(d) if a not in '01'),len(d))
 for k in range(lim+1):
  dp,ds=d[:k],d[k:];src=pre+p+'U';dst=dp+'Y';q=c.q;l,r=(src,dst) if left else (dst,src)
  for t in range(1,150):
   x=M.step(q,l,r)
   if x is None:break
   q,l,r=x;ns,nd=(l,r) if left else (r,l)
   if q==c.q and ns==pre+'U' and nd.startswith(dp) and nd.endswith('Y'):
    out=nd[k:-1]
    if out and set(out)<=set('01') and len(out)<=64:
     ns=pre+suf;nd=dp+'V'+ds
     yield t,C(q,*((ns,nd) if left else (nd,ns)),out),(left,pre,dp,suf,ds,p,out);break

def rotations(c):
 left='V'in c.l;s=c.l if left else c.r;pre,suf=s.split('V');p=c.p
 if pre and pre[-1]==p[-1]:
  b=pre[-1];ns=pre[:-1]+'V'+b+suf
  yield C(c.q,ns if left else c.l,c.r if left else ns,b+p[:-1]),('rotL',left,pre[:-1],b,p[:-1],suf)
 if suf and suf[0]==p[0]:
  b=suf[0];ns=pre+b+'V'+suf[1:]
  yield C(c.q,ns if left else c.l,c.r if left else ns,p[1:]+b),('rotR',left,pre,b,p[1:],suf[1:])

def equiv(c):
 seen={c};todo=deque([(c,[])])
 while todo:
  u,path=todo.popleft();yield u,path
  for v,info in rotations(u):
   if v not in seen and len(seen)<128:seen.add(v);todo.append((v,path+[(v,info)]))

def replay(M,start,target,a,b):
 c=start;ops=[];cost=[0,0];seen=set()
 for _ in range(2000):
  if cost[0]>a or cost[1]>b or c in seen:return
  eqs=list(equiv(c));seen.add(c)
  if tuple(cost)==(a,b):
   for v,path in eqs:
    if v==target:
     for v0,info in path:ops.append(('rotate',c,v0,info));c=v0
     return ops
  found=None
  for v,path in eqs:
   x=next(sweep(M,v),None)
   if x is not None and cost[0]+x[0]<=a:found=(v,path,x);break
  if found:
   v,path,(t,d,info)=found
   for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
   ops.append(('sweep',v,d,(t,info)));c=d;cost[0]+=t;continue
  for v,path in eqs:
   x=M.step(v.q,v.l,v.r)
   if x is not None and cost[1]<b:
    for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
    d=C(*x,v.p);ops.append(('step',v,d,1));c=d;cost[1]+=1;break
  else:return

def find_time(M,start,end,lim=2000):
 c=start
 for t in range(1,lim+1):
  c=M.step(*c)
  if c is None:return
  if c==end:return t

def find(M,start,target):
 times=[find_time(M,start.concrete(k),target.concrete(k)) for k in range(3)]
 if None in times:return
 b,t,u=times;a=t-b
 if a<0 or u!=2*a+b:return
 ops=replay(M,start,target,a,b)
 if ops is not None:return a,b,ops

def enc(s,z,o):return ''.join(o if b=='1' else z for b in s)
def init(M,L,m,z,o,e):
 c=(0,'','')
 for t in range(500):
  q,l,r=c
  if q==4 and l==L and r.startswith(m) and r.endswith(e):
   w=r[len(m):len(r)-len(e) if e else None]
   if len(w)%len(z)==0:
    chunks=[w[j:j+len(z)] for j in range(0,len(w),len(z))]
    if all(x in (z,o) for x in chunks):return t,''.join('1' if x==o else '0' for x in chunks)
  c=M.step(*c)
  if c is None:return

def trycase(M,L,m,z,o,e):
 ini=init(M,L,m,z,o,e)
 if ini is None:return
 stop=find(M,C(4,L,m+'V'+z+'X',o),C(4,L,m+'V'+o+'X',z))
 if stop is None:return
 for over in ('1','0','01','10','11','00',''):
  ov=find(M,C(4,L,m+'V'+e,o),C(4,L,m+'V'+enc(over,z,o)+e,z))
  if ov is not None:return ini,over,stop,ov

def cases(M):
 c=(0,'','');Ls=[]
 for t in range(250):
  q,l,r=c
  if q==4 and r.startswith('011') and len(l)<=18 and l not in Ls:Ls.append(l)
  c=M.step(*c)
  if c is None:break
 for L in Ls:
  for z,o in [('00000','00011'),('0000','0011'),('000','111'),('000','011'),('00','11'),('0','1')]:
   for e in ('','11','00011','011','1','0','000011'):
    ret=trycase(M,L,'011',z,o,e)
    if ret is not None:return (L,'011',z,o,e),ret

def w(s,p=None):
 if all(c in '01' for c in s):return '['+','.join('true' if c=='1' else 'false' for c in s)+']'
 xs=[];buf=''
 for c in s:
  if c in '01':buf+=c;continue
  if buf:xs.append(w(buf));buf=''
  if c=='V':xs.append(f'(rep {w(p)} n)')
  elif c=='X':xs.append('T')
  else:raise ValueError(c)
 if buf:xs.append(w(buf))
 return '('+' ++ '.join(xs)+')' if len(xs)>1 else xs[0]

def cfg(c):return f'⟨{c.q},{w(c.l,c.p)},{w(c.r,c.p)}⟩'
def prove(name,start,target,result,tail):
 a,b,ops=result;lines=[f'theorem {name} (n : Nat)'+(' (T : List Bool)' if tail else '')+f' : run0 table ({a}*n+{b}) {cfg(start)} = some {cfg(target)} := by'];cur=None;times=[];j=0;i=0
 while i<len(ops):
  kind,c,d,info=ops[i];i+=1
  if kind=='step':
   k=1
   while i<len(ops) and ops[i][0]=='step':d=ops[i][2];i+=1;k+=1
   time=str(k);proof='by rfl'
  elif kind=='sweep':
   k,(left,pre,dp,suf,ds,p,o)=info;lp,rp=(pre,dp) if left else (dp,pre);L,R=(suf,ds) if left else (ds,suf)
   time=f'({k}*n)';proof=f'by\n    simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using sweep{"L" if left else "R"} table {c.q} {w(lp)} {w(rp)} {w(p)} {w(o)} {k} (fun _ _ => rfl) n {w(L,c.p)} {w(R,c.p)}'
  elif kind=='rotate':
   typ,left,pre,bit,p,suf=info;arg=f'moveCut {w(pre)} {w(suf,c.p)} {w(p)} {str(bit=="1").lower()} n'
   if typ=='rotR':arg=f'({arg}).symm'
   f=f'fun x => (⟨{c.q},x,{w(c.r,c.p)}⟩ : Z0)' if left else f'fun x => (⟨{c.q},{w(c.l,c.p)},x⟩ : Z0)'
   lines.extend([f'  have e{j} : ({cfg(c)} : Z0) = {cfg(d)} := by',f'    simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using congrArg ({f}) ({arg})'])
   if cur is not None:lines.append(f'  rw [e{j}] at {cur}');j+=1;continue
   time='0';proof=f'by rw [e{j}]; rfl'
  else:raise ValueError(kind)
  lines.append(f'  have h{j} : run0 table {time} {cfg(c)} = some {cfg(d)} := {proof}');times.append(time)
  if cur is None:cur=f'h{j}'
  else:lines.append(f'  have g{j} := join0 {cur} h{j}');cur=f'g{j}'
  j+=1
 lines.extend([f'  rw [show {"+".join(times)}={a}*n+{b} by omega] at {cur}',f'  exact {cur}'])
 return '\n'.join(lines)

def gen(i,M,spec,ret,branch='ZeroRB'):
 L,m,z,o,e=spec;(entry,ini),over,stop,ov=ret
 ns=f'BB6.Agent8Raw54.{branch}.M{i}'
 lines=['import Raw54DigitSection','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.DigitSection','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for j,a in enumerate(M.a):
  if a=='---':continue
  b,r,q=a;lines.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(b=="1").lower()},{str(r=="R").lower()},{ord(q)-65}⟩)')
 lines.append('  | _,_ => none')
 lines.append(prove('stop',C(4,L,m+'V'+z+'X',o),C(4,L,m+'V'+o+'X',z),stop,True))
 lines.append(prove('overflow',C(4,L,m+'V'+e,o),C(4,L,m+'V'+enc(over,z,o)+e,z),ov,False))
 a,b=stop[:2];c,d=ov[:2]
 lines.extend([f'theorem never (M : Machine) (hm : compatible table M) : NeverHalts M := by',f'  apply BB6.Agent8Raw54.DigitSection.never table 4 {w(L)} {w(m)} {w(z)} {w(o)} {w(e)} {w(over)} {w(ini)} {entry} {a} {b} {c} {d} (by rfl) (by decide) (by decide) _ _ M hm',f'  · intro k T; simpa only [List.append_assoc,List.append_nil,List.nil_append] using stop k T',f'  · intro k; simpa only [enc,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using overflow k','#print axioms never',f'end {ns}'])
 return '\n'.join(lines)+'\n'

ZERO_RB_IDS=(1,3,83,86,97,101,102,103,129,130,131,132,133,134,135,136,137,138,150,163,164,170,180,206,249,265,290,312,361,365,366,367,381,397)

def emit(rows,out,ids=ZERO_RB_IDS,branch='ZeroRB'):
 for i in ids:
  M0=M(rows[i])
  if branch=='ZeroRB' and i in (103,367):
   spec=('0','011','00000','00011','000011')
   ret=trycase(M0,*spec)
  else:
   ans=cases(M0)
   assert ans is not None,i
   spec,ret=ans
  assert ret is not None,i
  out.joinpath(f'Raw54{branch}Digit{i}.lean').write_text(gen(i,M0,spec,ret,branch))

if __name__=='__main__':
 emit(Path(sys.argv[1]).read_text().splitlines(),Path(sys.argv[2]))
