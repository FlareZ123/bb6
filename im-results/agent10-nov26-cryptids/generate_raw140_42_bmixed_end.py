from pathlib import Path
s=Path(__file__).with_name('generate_raw140_42_mixed.py').read_text().split("print('import Raw14042Counter")[0]
exec(s)
print('import Raw14042BMixed\nnamespace Raw14042BMixedEndLocal\nopen BB6BlockFAR Raw140Orbit\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n')
name,q,d,L,R,q1,d1,L1,R1=('end0',4,0,'','19',1,1,'5','229');init=cfg(q,d,L,R);body=[];cost=[]
while (q,d,L,R)!=(q1,d1,L1,R1):
 assert len(body)<100
 st=R if d else L;b=st[:1] or '0';assert b not in '89'
 r,z,v,k=E[q,d,b];prev=cfg(q,d,L,R)
 l0,r0=(L,R[1:]) if d else (L[1:],R)
 L,R=(v+l0,r0) if z else (l0,v+r0)
 if L=='0':L=''
 if R=='0':R=''
 post=cfg(r,z,L,R);n=len(body)
 lemma=f'step{"R" if d else "L"} base {q} {r} {str(bool(z)).lower()} (S {b}) (S {v}) {k} {fmt(l0)} {fmt(r0)} (by rfl)'
 body.append(f'  have h{n} : run base {k} {prev} = some {post} := by\n    simpa only [ite_true, ite_false, Bool.false_eq_true,Szero,left_zero,right_zero] using {lemma}')
 cost.append(k);q,d=r,z
expr='h0'
for i in range(1,len(body)):expr=f'(join {expr} h{i})'
print(f'theorem {name} (Y : List Sym) : run base {sum(cost)} {init} = some {cfg(q,d,L,R)} := by\n'+ '\n'.join(body)+f'\n  exact {expr}\n')
print('end Raw14042BMixedEndLocal')
