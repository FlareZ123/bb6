from dataclasses import dataclass
from typing import Union

# Symbolic affine block-count generator for the M37 section return.
@dataclass(frozen=True)
class C:
    a:int=0; b:int=0
    def __add__(self,o): return C(self.a+o.a,self.b+o.b)
    def __sub__(self,o): return C(self.a-o.a,self.b-o.b)
    def lean(self):
        if self.a==0:return str(self.b)
        if self.a==1:return 'p' if self.b==0 else f'(p+{self.b})'
        return f'({self.a}*p+{self.b})'

def cnt(s):
    if s is None:return C(0,1)
    if s=='p':return C(1,0)
    if s.startswith('p+'):return C(1,int(s[2:]))
    return C(0,int(s))

Marker=str
Run=tuple[int,C]

def push(S:list[Union[Run,Marker]], a:int, c:C):
    if c==C(): return
    if not S and a==0 and c==C(0,1): return
    if S and isinstance(S[0],tuple) and S[0][0]==a:S[0]=(a,S[0][1]+c)
    else:S.insert(0,(a,c))

def pop(S,a,c):
    if not S:
        assert a==0 and c==C(0,1),(a,c,S);return
    z=S[0]; assert isinstance(z,tuple) and z[0]==a,(a,c,S)
    d=z[1]-c; assert d.a>=0 and d.b>=0,(a,c,S,d)
    S.pop(0)
    if d!=C():S.insert(0,(a,d))

def parse(s):
    S=[]
    for z in reversed(s.split()):
        if z=='X':S.insert(0,z);continue
        if '^' in z:a,n=z.split('^');c=cnt(n)
        else:a=int(z);c=C(0,1)
        push(S,int(a),c)
    return S

def fmt(S):
    if not S:return '[]'
    z=S[0]
    if isinstance(z,str):
        assert len(S)==1,S
        return z
    a,c=z;R=fmt(S[1:])
    if c.a:return f'(U {a} {c.lean()})' if len(S)==1 else f'(U {a} {c.lean()} ++ {R})'
    if c.b==0:return R
    pre=' :: '.join([f'S {a}']*c.b)
    return f'({pre} :: {R})'

def cfg(q,d,L,R):return f'boundary {q} {str(bool(d)).lower()} {fmt(L)} {fmt(R)}'

table=[7,21,11,12,15,1,6,18,4,17,17,24]
def exits():
    E={}
    for q in range(6):
      for d in range(2):
       for a in range(8):
        p=0 if d else 2;b=a;r=q;k=0
        while 0<=p<3 and k<145:
            cc=table[2*r+((b>>p)&1)]
            if cc==24:break
            b=(b&~(1<<p))|(((cc>>1)&1)<<p);r=cc>>2;p+=1 if cc&1 else -1;k+=1
        if p<0 or p>=3:E[q,d,a]=(r,1 if p>=3 else 0,b,k)
    return E
E=exits()

seq='''BL1 CR2 DR1 EL6 ER1 EL2 BL5 DL1 AR2 EL3^p+1 EL5 ER1 P^p+2 EL1 DR5 EL7 ER5^3 ER0 BL1 CR0 DL5 DL1 AR4 AR2 EL3^2 EL1 DR1 EL7 ER1 EL3^p+4 EL5 ER1 P^p+3 EL1 DR5 EL7 ER5^2 ER1 P EL1 DR5 EL7 ER5 ER0 BL1 CR0 DL5 DL3 EL3 EL1 DR1 EL7 ER1 EL3^p+5 EL5 ER1 P^p+4 EL1 DR5 EL7 ER5^3 ER4 BL1 CR4 DL5 DL1 AR4 AR6 EL3^2 EL1 DR1 EL7 ER1 EL3^p+6 EL5 ER1 P^p+5 EL1 DR5 EL7 ER5^2 ER1 EL1 DR5 EL7 ER5^2 ER2 BL1 CR2 DR0 BL6 BL5 DL1 AR2 EL3^2 EL1 DR1 EL7 ER1 EL3^p+7 EL5 ER1 P^p+6 EL1 DR5 EL7 ER5^2 ER1 P EL1 DR5 EL7 ER5 ER2 BL1 CR2 DR1 EL6 ER1 EL2 BL5 DL3 EL3 EL1 DR1 EL7 ER1 EL3^p+8 EL5 ER1 P^p+7 EL1 DR5 EL7 ER5^3 ER2'''.split()

L=parse('1 1 3^p 5 5 5 5 5 5 X');R=parse('2 1 5');q,d=1,0
body=[];costs=[]
for i,tok in enumerate(seq):
    pre=cfg(q,d,L,R)
    if tok.startswith('P'):
        n=cnt(tok.split('^',1)[1] if '^' in tok else None)
        assert q==4 and d==0
        pop(L,1,C(0,1));pop(R,5,C(0,1));pop(R,1,n)
        Xrest=list(L);Yrest=list(R)
        push(R,5,C(0,1));push(L,3,n);push(L,1,C(0,1))
        post=cfg(q,d,L,R);co=f'(19*{n.lean()})';costs.append(co)
        body.append(f'''  have h{i} : run M37 {co} ({pre}) = some ({post}) := by
    exact run_ext M37 (fill_extends _ _) _ _ _ (behindMany {n.lean()} {fmt(Xrest)} {fmt(Yrest)})''')
        continue
    src=tok.split('^')[0];n=cnt(tok.split('^',1)[1]) if '^' in tok else C(0,1)
    qq=ord(src[0])-65;dd=1 if src[1]=='R' else 0;a=int(src[2]);assert (q,d)==(qq,dd),(tok,q,d)
    r,z,b,k=E[q,d,a];side=R if d else L;pop(side,a,n);L0=list(L);R0=list(R)
    if z:push(L,b,n)
    else:push(R,b,n)
    post=cfg(r,z,L,R)
    if '^' in tok:
        assert r==q and z==d,(tok,(r,z),(q,d))
        co=f'({n.lean()}*{k})';lemma=f'sweep{src[1]} M37 {q} (S {a}) (S {b}) {k} {n.lean()} {fmt(L0)} {fmt(R0)} (by rfl)'
    else:
        co=str(k);lemma=f'step{src[1]} M37 {q} {r} {str(bool(z)).lower()} (S {a}) (S {b}) {k} {fmt(L0)} {fmt(R0)} (by rfl)'
    costs.append(co)
    body.append(f'''  have h{i} : run M37 {co} ({pre}) = some ({post}) := by
    simpa only [U, List.replicate_succ, List.replicate_zero, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using {lemma}''')
    q,d=r,z

assert (q,d)==(1,0)
expectedL=parse('1 1 1 3^p+8 X');expectedR=parse('2 1 5')
assert L==expectedL and R==expectedR
expr='h0'
for i in range(1,len(body)):expr=f'(join {expr} h{i})'
sumexpr='+'.join(costs)
prefix='''import Raw140VariantTransfer
namespace Raw14037Section
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary

theorem behindOne (X Y : List Sym) :
    run base 19 (boundary 4 false (S 1::X) (S 5::S 1::Y)) =
      some (boundary 4 false (S 1::S 3::X) (S 5::Y)) := by
  have h0 := stepL base 4 3 true (S 1) (S 7) 3 X (S 5::S 1::Y) (by rfl)
  have h1 := stepR base 3 4 false (S 5) (S 5) 1 (S 7::X) (S 1::Y) (by rfl)
  have h2 := stepL base 4 4 true (S 7) (S 3) 1 X (S 5::S 1::Y) (by rfl)
  have h3 := stepR base 4 4 true (S 5) (S 1) 7 (S 3::X) (S 1::Y) (by rfl)
  have h4 := stepR base 4 4 false (S 1) (S 5) 7 (S 1::S 3::X) Y (by rfl)
  exact join (join (join (join h0 h1) h2) h3) h4

theorem behindMany (n : Nat) (X Y : List Sym) :
    run base (19*n) (boundary 4 false (S 1::X) (S 5::(U 1 n ++ Y))) =
      some (boundary 4 false (S 1::(U 3 n ++ X)) (S 5::Y)) := by
  induction n generalizing X with
  | zero => simp [U, run]
  | succ n ih =>
    have h := join (behindOne X (U 1 n ++ Y)) (ih (S 3::X))
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc,
      show 19*(n+1)=19+19*n by omega] using h
'''
print(prefix)
startL=parse('1 1 3^p 5 5 5 5 5 5 X');startR=parse('2 1 5')
print('theorem section23_raw (p : Nat) (X : List Sym) :')
print(f'    run M37 ({sumexpr}) ({cfg(1,0,startL,startR)}) =')
print(f'      some ({cfg(1,0,expectedL,expectedR)}) := by')
print('\n'.join(body))
print(f'  exact {expr}')
print('\ntheorem section23 (p : Nat) (X : List Sym) :')
print(f'    run M37 (132*p+1099) ({cfg(1,0,startL,startR)}) =')
print(f'      some ({cfg(1,0,expectedL,expectedR)}) := by')
print('  have h := section23_raw p X')
print(f'  rw [show ({sumexpr}) = 132*p+1099 by omega] at h')
print('  exact h')
print('\n#print axioms behindMany\n#print axioms section23\nend Raw14037Section')
