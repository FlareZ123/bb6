"""Propose exact opaque-tail sweep recipes. Only generated Lean acceptance is proof."""
from pathlib import Path
import sys,json,itertools,collections
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'agent7-raw49'))
import emit_sweep_recipes as em

def concrete_step(p,z):
 q,l,r=z
 x=l[:1] or '0'
 if x=='?':raise ValueError('opaque left read')
 a=p[2*q+int(x)]
 if a=='---':raise ValueError('hole')
 q=ord(a[2])-65
 if a[1]=='R':
  x=r[:1] or '0'
  if x=='?':raise ValueError('opaque right read')
  return q,x+a[0]+l[1:],r[1:]
 return q,l[1:],a[0]+r

def options(p,z,maxcost=80):
 q,l,r=z
 for side,(a,b) in enumerate(((l,r),(r,l))):
  if len(a)<3:continue
  ap,w,*at=a
  for bpl in range(len(b[0])+1):
   bp,bt=b[0][:bpl],[b[0][bpl:]]+b[1:]
   zz=(q,ap+w+'?',bp+'?') if side==0 else (q,bp+'?',ap+w+'?')
   for k in range(1,maxcost+1):
    try:zz=concrete_step(p,zz)
    except ValueError:break
    if zz[0]!=q:continue
    sa,sb=zz[1:] if side==0 else zz[1:][::-1]
    if sa==ap+'?' and len(sb)==len(bp)+len(w)+1 and sb.startswith(bp) and sb.endswith('?'):
     o=sb[len(bp):-1]
     aa=em.pre(ap,at);bb=[bp,o]+bt
     znew=(q,aa,bb) if side==0 else (q,bb,aa)
     yield [side,len(ap),len(bp),o,k],znew

def same(z,goal):
 if z[0]!=goal[0]:return False
 try:
  for a,b in zip(z[1:],goal[1:]):em.equal_transforms(a,b)
  return True
 except AssertionError:return False

def solve(p,start,maxdepth=100):
 goal=(start[0],*[ [x+(a[j+1] if j+1<len(a) else '') if j%2==0 else x for j,x in enumerate(a)] for a in start[1:]])
 key=lambda z:(z[0],tuple(z[1]),tuple(z[2]))
 dq=collections.deque([(start,[])])
 seen={key(start)}
 while dq:
  z,act=dq.popleft()
  if act and same(z,goal):
   out=[]
   for x in act:
    if isinstance(x,int) and out and isinstance(out[-1],int):out[-1]+=x
    else:out.append(x)
   return out
  if len(act)>=maxdepth or sum(map(len,z[1]+z[2]))>150:continue
  for a,znew in options(p,z):
   k=key(znew)
   if k not in seen:seen.add(k);dq.append((znew,act+[a]))
  try:znew=em.step(p,z)
  except (AssertionError,ValueError):continue
  k=key(znew)
  if k not in seen:seen.add(k);dq.append((znew,act+[1]))
 return None

def discover(s,entry,period,idx):
 s=s.replace('_','');p=[s[i:i+3] for i in range(0,36,3)];z=(0,'','');zs=[]
 for t in range(entry+period+1):
  if t in (entry,entry+period):zs.append(z)
  if t<entry+period:z=concrete_step(p,z)
 a,b=zs
 assert a[0]==b[0]
 opts=[]
 for x,y in zip(a[1:],b[1:]):
  if x==y:opts.append([[x]]);continue
  d=len(y)-len(x);assert d>0
  opts.append([[x[:j],y[j:j+d],x[j:]] for j in range(len(x)+1) if y==x[:j]+y[j:j+d]+x[j:]])
 for l,r in itertools.product(*opts):
  start=(a[0],l,r);acts=solve(p,start)
  if acts:
   rec=[idx,s,entry,a[0],'|'.join(l),'|'.join(r),acts]
   em.emit(rec)
   return rec
 raise RuntimeError('no recurrence found')

if __name__=='__main__':
 s1='1RB---_1RC0RD_0RD0RE_0LD1LB_1LF1RA_1LF0LB'
 s2='1RB---_1RC0RD_0RD0RF_0LD1LB_1LE0LB_1LE1RA'
 for i,s in enumerate((s1,s2)):
  print(json.dumps(discover(s,12,31,i)))
