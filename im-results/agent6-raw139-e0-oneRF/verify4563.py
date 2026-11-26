"""Finite symbolic certificate for residual 4563/5.
L is nearest-first left of the head; R is nearest-first including the scan.
Literal trailing zeroes are interpreted as blank padding. A Rep(W,V) denotes
W repeated V times, for an arbitrary nonnegative integer V (X or Y).
The program proves the recurrence by exact prefix rewrites and finite guarded
block transfers. It does not use a simulation cutoff as a nonhalting argument.
"""
from collections import Counter, deque
from dataclasses import dataclass
import time

TABLE = [7,17,11,5,14,8,24,16,23,11,3,17]
P=''.join(('1' if a>0 else '0')*abs(a) for a in [-1,2,-1,2,-1,2,-2,3,-1,7,-1,2,-5,3])
M0=''.join(('1' if a>0 else '0')*abs(a) for a in [-1,1,-1,4,-1,6,-2,3])
M1=''.join(('1' if a>0 else '0')*abs(a) for a in [-1,7,-1,4,-1,6,-2,3])
U=M1+M0*5
Q='01111101111'
K='0111111'

def family(x,y):return P+M0+U*x+M1+M0*6+Q+K*y

def raw(q,l,r,n,guard=False):
 l,r=deque(map(int,l)),deque(map(int,r))
 for t in range(n):
  assert not guard or r,('unknown scan',t)
  a=r.popleft() if r else 0
  v=TABLE[2*q+a]
  assert v!=24,('undefined transition',t,q,a)
  w=v>>1&1
  if v&1:l.appendleft(w)
  else:
   assert not guard or l,('unknown left cell',t)
   r.appendleft(w);r.appendleft(l.popleft() if l else 0)
  q=v>>2
 return q,''.join(map(str,l)),''.join(map(str,r))

def macro(l,r):
 # Each rule returns consumed L/R prefixes, produced L/R prefixes, cost.
 if r.startswith('01'):return '', '01', '01', '', 2
 if r.startswith('001'):return '', '001', '011', '', 3
 if r.startswith('10'):
  a=l[0] if l else '0';return a,'10','',a+'01',3
 if r.startswith('11'):
  a=(l+'000')[:3];assert a.startswith('01'),(l,r);return a,'11','',a[-1]+'0100',5
 assert r.startswith('000'),(l,r)
 n=0
 while 3+n<len(r) and r[3+n]=='1':n+=1
 gap=r[3+n:5+n]
 if gap=='00':
  if n==0:return '','00000','11','101',6
  return '', '000'+'1'*n+'00', '0'*(n-1)+'111','001',n+6
 assert gap=='01'
 if n==0:
  a=(l+'000')[:3];assert a.startswith('01'),(l,r);return a,'00001','',a[-1]+'0100000',11
 if n==1:return '','000101','1','10100',9
 raise ValueError(('D0',l,r))

@dataclass(frozen=True)
class Rep:
 w:str
 v:str
 def __repr__(self):return f'({self.w})^{self.v}'

def norm(xs):
 out=[]
 for x in xs:
  if isinstance(x,str):
   if not x:continue
   if out and isinstance(out[-1],str):out[-1]+=x
   else:out.append(x)
  else:out.append(x)
 if out and isinstance(out[-1],str):
  out[-1]=out[-1].rstrip('0')
  if not out[-1]:out.pop()
 return out

def literal(xs):return ''.join(x for x in xs if isinstance(x,str))
def pref(xs,n=100000):
 # known prefix, followed by arbitrary blank padding if no symbolic marker.
 if not xs:return '0'*min(n,100)
 if isinstance(xs[0],Rep):return ''
 if len(xs)==1:return (xs[0]+'0'*min(n,100))[:n]
 return xs[0][:n]

def split(xs):
 if not xs:return '',None,[]
 if isinstance(xs[0],Rep):return '',xs[0],xs[1:]
 if len(xs)==1:return xs[0],None,[]
 return xs[0],xs[1],xs[2:]

def consume(xs,w,out):
 a,m,rest=split(xs)
 if m is None:
  assert (a+'0'*len(w)).startswith(w),(xs,w)
  return norm([out+a[len(w):]])
 assert a.startswith(w),(xs,w)
 return norm([out+a[len(w):],m,*rest])

def inst(xs,x=0,y=0):return ''.join(w if isinstance(w,str) else w.w*(x if w.v=='X' else y) for w in xs)

def repform(xs):return '|'.join(map(str,xs))

# exact prefix rule: reject if would consult an unknown suffix.
def guarded(l,r):
 try:a,b,c,d,t=macro(l,r)
 except (AssertionError,IndexError,ValueError):return None
 if not l.startswith(a) or not r.startswith(b):return None
 return a,b,c,d,t

# Find an exact local transfer of one variable block. Other-side minimal
# touched original prefix determines the fixed prefix retained in the loop.
# Returns source prefix A (unchanged), other prefix C, produced V, cost.
cache={};failcache=set();loopdata={}
def findloop(side,A,W,C,limit=3000):
 key=(side,A,W,C[:256]);
 if key in cache:return cache[key]
 if key in failcache:return None
 C=C[:256]
 l,r=(A+W,C) if side==0 else (C,A+W)
 consumed=0;generated=0;cost=0;trace=[]
 for i in range(limit):
  h=guarded(l,r)
  if h is None:break
  a,b,c,d,dt=h;trace.append(h)
  if side==0:
   take=len(b);give=len(d)
  else:take=len(a);give=len(c)
  consumed+=max(0,take-generated);generated=max(0,generated-take)+give
  l=c+l[len(a):];r=d+r[len(b):];cost+=dt
  s,o=(l,r) if side==0 else (r,l)
  if s==A:
   fixed=C[:consumed];tail=C[consumed:]
   assert o[generated:]==tail,(side,A,W,C,o,generated,consumed)
   if o[:generated].startswith(fixed):
    V=o[len(fixed):generated]
    # if V empty, still valid (erases variable block)
    ans=(fixed,V,cost,i+1);cache[key]=ans
    # Independently check the exact primitive loop with both tails guarded.
    src=(A+W,fixed) if side==0 else (fixed,A+W)
    dst=(A,fixed+V) if side==0 else (fixed+V,A)
    assert raw(4,*src,cost,True)==(4,*dst)
    loopdata[(side,A,W,fixed,V,cost)]=trace.copy()
    return ans
  if len(l)+len(r)>len(A+W+C)+1024:break
 failcache.add(key);return None

def rotations(xs):
 A,m,tail=split(xs);assert m is not None
 W=m.w
 yield xs,0
 # Move a suffix of A across variable block (rotate right).
 for i in range(1,min(len(A),len(W))+1):
  if A[-i:]==W[-i:]:
   yield norm([A[:-i],Rep(W[-i:]+W[:-i],m.v),W[-i:],*tail]),-i
 # Move a prefix of following known literal across variable block.
 D,n,rest=split(tail)
 for i in range(1,len(W)+1):
  d=D+'0'*i if n is None else D
  if d[:i]==W[:i]:
   yield norm([A+W[:i],Rep(W[i:]+W[:i],m.v),D[i:],*([n,*rest] if n is not None else [])]),i
  else:break

# A transfer can be applied before the macro would consume the marker.
# Its repetition is valid for every nonnegative value of the marker.
def transfer(L,R,side):
 S,O=(L,R) if side==0 else (R,L)
 C= pref(O,256)
 for SS,rot in rotations(S):
  A,m,T=split(SS)
  if len(A)>64:continue
  res=findloop(side,A,m.w,C)
  if res is None:continue
  fixed,V,cost,n=res
  OS=consume(O,fixed,fixed) # verify prefix available
  a,b,c=split(OS)
  assert a.startswith(fixed) or b is None and (a+'0'*len(fixed)).startswith(fixed)
  # Preserve original word after fixed prefix; variable output insertion.
  after=norm([a[len(fixed):],*([b,*c] if b is not None else [])])
  newO=norm([fixed,*([Rep(V,m.v)] if V else []),*after])
  newS=norm([A,*T])
  # base instance is unchanged; rotation and transfers affect only variable counts.
  assert literal(newO)==literal(O) and literal(newS)==literal(S),(side,S,O,newS,newO)
  return (newS,newO,m.v,cost,n,(side,A,m.w,fixed,V,cost,rot)) if side==0 else (newO,newS,m.v,cost,n,(side,A,m.w,fixed,V,cost,rot))
 return None

def common_rotation(S,w):
 for SS,rot in rotations(S):
  if rot and pref(SS,len(w)).startswith(w):return SS
 return None

def sweep(L,R):
 # ordinary constant block transfers using exact 29- and 19-step rules.
 A=split(L)[0];C=split(R)[0]
 if A.startswith('1111110') and C.startswith('101'):
  n=0
  while A.startswith('1111110',7*n):n+=1
  return consume(L,'1111110'*n,''),consume(R,'101','101'+'0011111'*n),29*n,n
 if C.startswith('00110011111'):
  n=0
  while C.startswith('0011111',4+7*n):n+=1
  return consume(L,'',K*n),consume(R,'0011'+'0011111'*n,'0011'),19*n,n
 return None


def prove_period():
 # initial family: P M0 (M1 M0^5)^X M1 M0^6 Q K^Y
 L=norm([P+M0,Rep(U,'X'),M1+M0*6+Q,Rep(K,'Y')]);R=[]
 expected=norm([P+M0+U,Rep(U,'X'),M1+M0*6+Q+K*553,Rep(K,'Y')])
 # normalization can shift fixed copies across equal marker.
 count=Counter();cost=Counter();transfers=Counter();cleans=0;i=0;start=time.time();history=[]
 while cleans<145:
  i+=1
  s=sweep(L,R)
  if s:
   L,R,dt,n=s;cost['c']+=dt;count['sweep']+=1
  else:
   l,r=literal(L),literal(R)
   a,b,c,d,dt=macro(l+'000',r+'00000')
   touched=[]
   if not pref(L,len(a)).startswith(a):touched.append(0)
   if not pref(R,len(b)).startswith(b):touched.append(1)
   if touched:
    success=False
    for side in touched:
     S=L if side==0 else R;w=a if side==0 else b
     # prefer finite prefix rotation if it exposes full needed prefix
     SS=common_rotation(S,w)
     if SS is not None:
      if side==0:L=SS
      else:R=SS
      count['rotation']+=1;success=True;break
     h=transfer(L,R,side)
     if h:
      L,R,v,dc,n,info=h;cost[v]+=dc;transfers[info]+=1;count['transfer']+=1;success=True
      break
    if success:continue
    raise AssertionError(('symbolic step stuck',i,cleans,touched,(a,b,c,d,dt),L,R))
   L=consume(L,a,c);R=consume(R,b,d);cost['c']+=dt;count['macro']+=1
  if not R:
   cleans+=1
 assert not R and cleans==145
 assert dict(cost)=={'c':24481769,'X':1294020,'Y':79632}
 # Canonicalize the two marker locations by the exact identity
 # W^n D = D rot(W,|D|)^n when D is a prefix of W^infinity.
 for pos in (1,3):
  a,m,b=L[pos-1:pos+2]
  target=expected[pos-1]
  assert isinstance(m,Rep) and isinstance(a,str) and isinstance(b,str)
  d=len(target)-len(a)
  assert d>=0 and b[:d]==(m.w*((d+len(m.w)-1)//len(m.w)))[:d]
  k=d%len(m.w)
  L[pos-1:pos+2]=[a+b[:d],Rep(m.w[k:]+m.w[:k],m.v),b[d:]]
 assert norm(L)==expected,(L,expected)
 assert len(loopdata)==19
 print('EXACT recurrence: (X,Y) -> (X+1,Y+553); cost',dict(cost),flush=True)
 print('Symbolic event counts',dict(count),'; 19 independently guarded primitive loops',flush=True)

if __name__=='__main__':
 q,l,r=raw(0,'','',28792194)
 assert q==4 and l.rstrip('0')==family(0,619) and not r.rstrip('0')
 print('Authentic blank-start seed at step 28792194 verified.',flush=True)
 # Independent checks of fixed prefix transfer lemmas.
 assert raw(4,'1111110','101',29,True)==(4,'','1010011111')
 assert raw(4,'','00110011111',19,True)==(4,'0111111','0011')
 prove_period()
