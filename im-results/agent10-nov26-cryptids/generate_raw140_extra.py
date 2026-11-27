"""Emit exact entry paths for 15 new growth cylinders, in bounded kernel chunks.
No computation is trusted: each chunk is checked by Lean execute/execute_sound.
The first five and row 11 are exact residual tables; others are refinements.
"""
from pathlib import Path
from functools import lru_cache
from itertools import groupby

DIR = Path(__file__).resolve().parent
# A1,F0, macro steps after initial 2, raw steps incl initial 2, n, phase, raw140 residual index
ROWS = [
 (4,24,28262,81948,135,0,566),
 (10,24,2514,7298,40,0,602),
 (11,24,2512,7292,40,0,608),
 (15,24,2510,7284,40,0,609),
 (17,24,2514,7294,40,0,575),
 (20,5,2512,7294,40,0,570),
 (20,8,23930,68838,123,1,570),
 (20,9,2510,7286,40,0,570),
 (20,11,28262,81948,135,0,570),
 (20,14,28282,81998,135,0,570),
 (20,17,28262,81958,135,0,570),
 (21,16,28264,81958,135,0,580),
 (22,15,2514,7298,40,0,605),
 (22,16,2514,7302,40,0,605),
 (22,17,2514,7296,40,0,605),
]
CHUNK=512

def codes(a,f):return (7,a,11,12,15,1,6,18,4,17,f,24)

def opt(c):
    if c==24:return 'none'
    return f'(some ⟨{str(bool(c//2%2)).lower()},{str(bool(c%2)).lower()},{c//4}⟩)'

@lru_cache(None)
def local_exit(M,q,d,a):
    pos=0 if d else 2
    seen=set(); k=0
    while 0<=pos<3:
        key=q,pos,a
        assert key not in seen and k<145
        seen.add(key); b=(a>>pos)&1; c=M[2*q+b]
        assert c<24, (M,q,d,a)
        a=(a&~(1<<pos))|((c//2%2)<<pos)
        pos+=1 if c%2 else -1; q=c//4; k+=1
    return k,q,pos==3,a

def adv(M,state):
    q,d,L,R=state
    a=(R[0] if R else 0) if d else (L[0] if L else 0)
    if d:R=R[1:]
    else:L=L[1:]
    k,q,d,b=local_exit(M,q,d,a)
    if d:
        if L or b:L=(b,)+L
    else:
        if R or b:R=(b,)+R
    return k,(q,d,L,R)

def fmt_stack(xs):
    terms=[]
    for a,g in groupby(xs):
        n=len(list(g)); terms.append(f'(U {a} {n})' if n>2 else '['+','.join(f'S {a}' for _ in range(n))+']')
    return '('+' ++ '.join(terms)+')' if terms else '[]'

def fmt(s):
    q,d,L,R=s
    return f'⟨{q},{str(d).lower()},{fmt_stack(L)},{fmt_stack(R)}⟩'

def build(i,row):
    a,f,k,t,n,phase,ancestor=row
    M=codes(a,f); name=f'X{i}'
    out=['import Raw140ExtraCore','namespace Raw140Extra.'+name,'open BB6BlockFAR Raw140Orbit',
         'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
         f'def M : Table := fill {opt(a)} {opt(f)}',
         f'theorem ext : Extends M := fill_extends {opt(a)} {opt(f)}',
         'def s0 : BState := start']
    state=(2,True,(6,),()); total=2; j=0; done=0
    edges=[]
    while done<k:
        length=min(CHUNK,k-done); cost=0
        for _ in range(length):
            c,state=adv(M,state);cost+=c
        j+=1;done+=length;total+=cost
        out.append(f'def s{j} : BState := {fmt(state)}')
        out.append(f'theorem e{j} : execute M {length} s{j-1} = some ({cost},s{j}) := by decide +kernel')
        edges.append((j,length,cost))
    assert total==t and state==(1,True,(5,),(2,)*n+((4,2) if phase else (1,5))), (i,total,state)
    label='B' if phase else 'A'
    out.append(f'theorem entry : run M {t} primBlank = some (family{label} {n}) := by')
    out.append('  have h0 := run_ext M ext _ _ _ base_start')
    for j,length,cost in edges:
        out.append(f'  have h{j} := join h{j-1} (execute_sound M {length} {cost} s{j-1} s{j} e{j})')
    out.append(f'  change run M {t} primBlank = some (family{label} {n}) at h{j}')
    out.append(f'  exact h{j}')
    out.append(f'theorem forever (k : Nat) : ∃ c, run M k primBlank = some c := forever{label} M ext {t} {n} entry k')
    out.append('#print axioms forever')
    out.append('end Raw140Extra.'+name)
    (DIR/f'Raw140Extra{i:02d}.lean').write_text('\n'.join(out)+'\n')

if __name__=='__main__':
    for i,row in enumerate(ROWS):build(i,row)
    print('Generated',len(ROWS),'exact entry proof modules.')
