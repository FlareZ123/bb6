from pathlib import Path
# count is either n+k or constant k; segments grouped and nearest-first.
A=[('BR2','BR5',3,'n'),('BR1','DL0',1),('DL5','DL4',3,'n+1'),('DL0','AR2',3),('AR4','AR3',3,'n+1'),('AR0','DR7',3),('DR5','EL5',1),('EL7','ER3',1),('ER5','ER1',7),('ER0','BL0',1),('BL1','CR5',1),('CR0','DL2',3),('DL5','DL4',3),('DL3','EL5',3),('EL3','EL1',3,'n+1'),('EL2','BL1',3),('BL0','CR4',1),('CR1','CR6',3,'n+2'),('CR5','BL2',5),('BL6','BL2',3,'n+2'),('BL4','BR5',5)]
B=[('BR2','BR5',3,'n'),('BR4','ER1',5),('ER2','BL2',1),('BL1','CR5',1),('CR2','DR6',7),('DR0','BL1',1),('BL6','BL2',3),('BL5','DL2',3),('DL5','DL4',3,'n+1'),('DL0','AR2',3),('AR4','AR3',3,'n+1'),('AR2','EL1',3),('EL3','EL1',3,'n+1'),('EL2','BL1',3),('BL0','CR4',1),('CR1','CR6',3,'n+3'),('CR2','DR6',7),('DR1','EL1',1),('EL6','ER2',1),('ER1','EL5',7),('EL2','BL1',3),('BL6','BL2',3,'n+3'),('BL4','BR5',5)]

def count(s):return (1,int(s[2:]) if '+' in s else 0) if 'n' in s else (0,int(s))
def show(c):return ('n' if c[1]==0 else f'(n+{c[1]})') if c[0] else str(c[1])
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def minus(a,b):return tuple(x-y for x,y in zip(a,b))
def pop(xs,a,c):
 if not xs:assert a==0 and c==(0,1);return []
 b,d=xs[0];assert a==b,(a,b,xs)
 k=minus(d,c);assert k[0]>=0 and k[1]>=0,(xs,c,k)
 return ([(b,k)] if k!=(0,0) else [])+xs[1:]
def push(xs,a,c):
 if not xs and a==0:return []
 if xs and xs[0][0]==a:return [(a,plus(c,xs[0][1]))]+xs[1:]
 return [(a,c)]+xs

def fmt(xs):
 if not xs:return '[]'
 a,c=xs[0]
 if c[0]:return f'(U {a} {show(c)} ++ {fmt(xs[1:])})' if xs[1:] else f'(U {a} {show(c)})'
 return '('+' :: '.join([f'S {a}']*c[1])+f' :: {fmt(xs[1:])})'
def cfg(q,d,L,R):return f'boundary {ord(q)-65} {str(d=="R").lower()} {fmt(L)} {fmt(R)}'

def phase(name,seq):
 q,d='B','R';L=[(5,(0,1))];R=[(2,(1,0)),(1,(0,1)),(5,(0,1))] if name=='A' else [(2,(1,0)),(4,(0,1)),(2,(0,1))]
 costs=[]
 out=[f'theorem phase{name} (n : Nat) : run base (18*n+{62 if name=="A" else 82}) (family{name} n) = some (family{"B" if name=="A" else "A"} (n+3)) := by']
 for i,(src,dst,k,*cnt) in enumerate(seq):
  assert (q,d)==tuple(src[:2]);a=int(src[2]);b=int(dst[2]);c=count(cnt[0]) if cnt else (0,1)
  before=cfg(q,d,L,R)
  L0=pop(L,a,c) if d=='L' else L;R0=pop(R,a,c) if d=='R' else R
  q2,d2=dst[:2];L2=push(L0,b,c) if d2=='R' else L0;R2=push(R0,b,c) if d2=='L' else R0
  after=cfg(q2,d2,L2,R2)
  if cnt:lemma=f'sweep{d} base {ord(q)-65} (S {a}) (S {b}) {k} {show(c)} {fmt(L0)} {fmt(R0)} (by rfl)';cost=f'({show(c)}*{k})'
  else:lemma=f'step{d} base {ord(q)-65} {ord(q2)-65} {str(d2=="R").lower()} (S {a}) (S {b}) {k} {fmt(L0)} {fmt(R0)} (by rfl)';cost=str(k)
  costs.append(cost)
  out.extend([f'  have h{i} : run base {cost} ({before}) = some ({after}) := by', f'    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using {lemma}'])
  L,R,q,d=L2,R2,q2,d2
 assert q=='B' and d=='R' and L==[(5,(0,1))]
 print('end',name,R)
 expr='h0'
 for i in range(1,len(seq)):expr=f'(join {expr} h{i})'
 out.append(f'  have H := {expr}')
 out.append(f'  change run base _ (family{name} n) = some (family{"B" if name=="A" else "A"} (n+3)) at H')
 out.append(f'  rw [show ({"+".join(costs)}) = 18*n+{62 if name=="A" else 82} by omega] at H')
 out.append('  exact H')
 return '\n'.join(out)
Path(__file__).with_name('Raw140OrbitPhases.lean').write_text('import Raw140OrbitCore\nnamespace Raw140Orbit\nopen BB6BlockFAR\nset_option maxRecDepth 3000\nset_option maxHeartbeats 500000\n'+phase('A',A)+'\n\n'+phase('B',B)+'\nend Raw140Orbit\n')
