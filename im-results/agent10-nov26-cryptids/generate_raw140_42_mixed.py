# Exact finite-context generator for the common nine-row table.
def exits(a,f):
 t=[7,a,11,12,15,1,6,18,4,17,f,24]; E={}
 for q in range(6):
  for d in range(2):
   for b in range(8):
    p=0 if d else 2;r=q;s=b;k=0
    while 0<=p<3 and k<145:
     c=t[2*r+((s>>p)&1)]
     if c==24: break
     s=(s&~(1<<p))|(((c>>1)&1)<<p);r=c>>2;p+=1 if c&1 else -1;k+=1
    if p<0 or p>=3:E[q,d,str(b)]=(r,int(p>=3),str(s),k)
 return E

E=exits(24,24)
SPECS=[('front44',4,1,'28','34649',2,1,'45268','49'),('front46',4,1,'28','34669',2,1,'45268','69'),('back4',3,0,'55268','9',1,0,'8','25449'),('front5',4,1,'28','3549',1,0,'8','22469'),('eOne66',1,1,'58','4669',2,1,'4558','69')]
def fmt(w):
 if not w:return '[]'
 if w[0]=='8':assert w=='8';return 'X'
 if w[0]=='9':assert w=='9';return 'Y'
 return '(S '+w[0]+' :: '+fmt(w[1:])+')'
def cfg(q,d,L,R):return f'(boundary {q} {str(bool(d)).lower()} {fmt(L)} {fmt(R)})'
def gen(spec):
 name,q,d,L,R,q1,d1,L1,R1=spec
 init=cfg(q,d,L,R);body=[];cost=[]
 while (q,d,L,R)!=(q1,d1,L1,R1):
  assert len(body)<200
  st=R if d else L;b=st[0];assert b not in '89'
  r,z,v,k=E[q,d,b];prev=cfg(q,d,L,R)
  l0,r0=(L,R[1:]) if d else (L[1:],R)
  L,R=(v+l0,r0) if z else (l0,v+r0)
  post=cfg(r,z,L,R);n=len(body)
  lemma=f'step{"R" if d else "L"} base {q} {r} {str(bool(z)).lower()} (S {b}) (S {v}) {k} {fmt(l0)} {fmt(r0)} (by rfl)'
  body.append(f'  have h{n} : run base {k} {prev} = some {post} := by\n    simpa only [ite_true, ite_false, Bool.false_eq_true] using {lemma}')
  cost.append(k);q,d=r,z
 expr='h0'
 for i in range(1,len(body)):expr=f'(join {expr} h{i})'
 return f'theorem {name} (X Y : List Sym) : run base {sum(cost)} {init} = some {cfg(q,d,L,R)} := by\n'+ '\n'.join(body)+f'\n  exact {expr}\n'
print('import Raw14042Counter\nnamespace Raw14042MixedLocal\nopen BB6BlockFAR Raw140Orbit\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n')
for spec in SPECS: print(gen(spec))
print('end Raw14042MixedLocal')
