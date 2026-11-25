"""Two-query Raw41 partition, candidate discovery only. Lean checks the entire tree."""
from pathlib import Path
from collections import Counter,defaultdict
import re
P='1RB---_1RC---_0RD---_1LD1RA_------_------'.replace('_','')
T=tuple(-1 if P[i]=='-' else (int(P[i])*12+6*(P[i+1]=='R')+ord(P[i+2])-65) for i in range(0,36,3))
def move(i):return str(i//12)+'LR'[i%12>=6]+chr(65+i%6)
def show(p):return '_'.join(''.join('---' if k<0 else move(k) for k in p[i:i+2]) for i in range(0,12,2))
def mv(i):return f'⟨{str(i>=12).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def slot(i):return f'({i//2},{str(bool(i%2)).lower()})'
def refine(p,s,i):return p[:s]+(i,)+p[s+1:]
def classify(p,L=1000):
    q=h=0;tape=set();prev=defaultdict(list);tr=[]
    for n in range(L+1):
        s=q*2+(h in tape)
        if p[s]<0:return ('query',n,s)
        lo=hi=h;i=n-1
        for j in reversed(prev[q]):
            if n-j>256:break
            while i>=j:lo=min(lo,tr[i][1]);hi=max(hi,tr[i][1]);i-=1
            _,h0,t0=tr[j];d=h-h0
            if d>=0 and {x for x in t0 if x>=lo}=={x-d for x in tape if x-d>=lo}:return ('cycle',j,n-j,True,lo)
            if d<=0 and {x for x in t0 if x<=hi}=={x-d for x in tape if x-d<=hi}:return ('cycle',j,n-j,False,hi)
        prev[q].append(n);tr.append((q,h,frozenset(tape)))
        a=p[s];tape.add(h) if a>=12 else tape.discard(h);h+=1 if a%12>=6 else -1;q=a%6
    return ('open',)

def far(code,p):
    rev=int(code[0]);D=list(map(int,code[1:]));n=len(D)//2;N=6*n+1;H=N-1;halt=1<<H;T=[0]*(2*N);T[H]=T[N+H]=halt;rules=[]
    for l in range(n):
        for q in range(6):
            for a in range(2):
                m=p[2*q+a];dst=a*N+6*l+q
                if m<0: T[dst]=halt;continue
                w,r,k=m//12,m%12>=6,m%6
                if r!=rev:T[dst]=1<<(6*D[2*l+w]+k)
                else:
                    for j in range(n):
                        for b in range(2):
                            if D[2*j+b]==l:rules.append((dst,b*N+6*j+k,w*N))
    while True:
        z=halt
        while True:
            old=z
            for j in range(N):
                if T[j]&z:z|=1<<j
            assert not z&1,(code,p)
            if old==z:break
        changed=False
        for dst,src,off in rules:
            v=T[dst];bits=T[src]
            while bits:
                k=(bits&-bits).bit_length()-1;v|=T[off+k];bits&=bits-1
            if v!=T[dst]:T[dst]=v;changed=True
        if not changed:return f'.far {str(bool(rev)).lower()} {n} ⟨0,{D},{T[:N]},{T[N:]},{z}⟩'

# Reproducible candidate bank hits for the five open second-level cylinders.
FAR={24:'0012101',200:'000',291:'00101',307:'000',488:'000'}
raw=Counter();canonical=Counter();residual=[];data=[]
def support(p):return max(2,max(max(i//2,k%6)+1 for i,k in enumerate(p) if k>=0))
def cycle(a):return f'.closed (.cycle {a[1]} {a[2]} {str(a[3]).lower()} ({a[4]}))'
B=16
head='''import Raw41LBLA
import PartialAudit
import ZipPrefixAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
'''
lines=[head]
a=classify(T);assert a==('query',6,1)
for i in range(24):
    p=refine(T,1,i);a=classify(p);can=i%6<=4
    if a[0]=='cycle':
        raw['first_cycle']+=1;canonical['first_cycle']+=int(can);tree=cycle(a)
    else:
        assert a[0]=='query';raw['second_split']+=1;canonical['second_split']+=int(can);n,s=a[1:];kids=[]
        for j in range(24):
            t=refine(p,s,j);r=classify(t);can2=can and j%6<=support(p)
            if r[0]=='cycle':
                raw['second_cycle']+=1;canonical['second_cycle']+=int(can2);kids.append(cycle(r))
            elif r[0]=='open':
                code=FAR[i*24+j];raw['second_far']+=1;canonical['second_far']+=int(can2);kids.append('.closed ('+far(code,t)+')');data.append((move(i),move(j),show(t),code))
            else:
                assert r[0]=='query';raw['residual']+=1;canonical['residual']+=int(can2);kids.append('.unresolved');residual.append((move(i),move(j),show(t)))
        tree=f'.split {n} {slot(s)} (byPartialMove [\n'+',\n'.join(kids)+'])'
    lines.append(f'\ndef kid{i:02} : PartialAudit := {tree}\ntheorem kid{i:02}_checked : partialCheck {B} (child {mv(i)}) kid{i:02} = true := by decide +kernel\n')
lines.append(f'\ndef kids : Move → PartialAudit := byPartialMove [{",".join(f"kid{i:02}" for i in range(24))}]\ndef tree : PartialAudit := .split 6 (0,true) kids\n')
lines.append(f'''theorem kids_checked (mv : Move) : partialCheck {B} (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
''')
for q in range(6):
    for w,r in [(0,0),(0,1),(1,0),(1,1)]:lines.append(f'  · exact kid{12*w+6*r+q:02}_checked\n')
lines.append(f'''
theorem checked : partialCheck {B} parent tree = true := by
  change (zipQueryOK {B} parent 6 (0,true) && allMoves (fun mv => partialCheck {B} (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids_checked⟩

def residuals := partialResiduals parent tree

theorem residual_count : residuals.length = {raw['residual']} := by decide +kernel

theorem sound : ∀ m, compatible parent m → WeightedBound {B} m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound {B} parent tree parent_root parent_nohalt checked

#print axioms checked
#print axioms residual_count
#print axioms sound
end BB6.Agent47Raw41
''')
Path('Raw41TwoCut.lean').write_text(''.join(lines));print('raw',dict(raw),'canonical',dict(canonical),'FAR',data,'source bytes',Path('Raw41TwoCut.lean').stat().st_size)
