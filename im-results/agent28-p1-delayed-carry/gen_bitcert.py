"""Untrusted endpoint-partition proposals; the generated Lean checks all data."""
import sys
from functools import lru_cache

def target(n,i,B): return 0 if i<n else ((7*B)>>(i-n))&1

def bits_iter(b):
    while b:
        lo=b&-b; yield lo.bit_length()-1; b^=lo

@lru_cache(None)
def masks(L):
    return [((1 << (2*(1<<L)))-1)//((1<<(1<<k))+1) for k in range(L+1)]

def forward(n,B,s,h,bits):
    L=(n+s+h+3).bit_length(); m=masks(L)
    for i in range(s,s+h):
        y=target(n,i,B); C=n+i+3
        x=((bits | (bits<<C))>>y)&m[0]
        for k in range(L): x=(x|(x>>(1<<k)))&m[k+1]
        bits=x
        if bits==0: break
    return bits

def partitions(n,B,s,h,ends):
    g={c:1<<c for c in bits_iter(ends)}
    for i in range(s+n-1,s+h-1,-1):
        C=n+i+3; y=target(n,i,B); gg={}
        for c,b in g.items():
            a=(2*c+y)%C; gg[a]=gg.get(a,0)|b
        g=gg
    for a,b in sorted(g.items()):
        c=a; W=B
        for i in range(s+h-1,s-1,-1):
            x,c=divmod(2*c+target(n,i,B),n+i+3); W+=x<<i
        yield (W,a,b),c

def lit(g): return f'⟨{hex(g[0])}, {g[1]}, {hex(g[2])}⟩'
def glit(gs): return '['+', '.join(map(lit,gs))+']'

def main(n,K,hmax):
    assert n>=14 and n%2==0 and K>n and 0<hmax<=n
    L=(n+K+3).bit_length(); s=1; a=(n+2)//2
    groups=[(1,a,forward(n,1,1,n,1<<a))]
    out=['import BitGroupCert','open BB6.Agent28BitGroup BB6.Agent45.DelayedCarry','set_option maxRecDepth 1000000','set_option maxHeartbeats 0',f'def g0 : List BitGroup := {glit(groups)}',f'theorem first_eq : bitFirst {L} {n}=g0 := by decide +kernel',f'theorem c0 : BitCert {n} {K} 1 g0 := first_eq ▸ bit_cert_first {L} {n} {K} (by decide) (by decide)']
    t=0
    while groups and s+n<K:
        h=min(hmax,K-n-s); plans=[]; nxt=[]
        for g in groups:
            B,a,b=g; pp=[]
            for p,ac in partitions(n,B,s,h,b):
                assert a==ac; W,c,ends=p; pp.append(p)
                new=forward(n,W,s+n,h,ends)
                if new: nxt.append((W,c,new))
            plans.append((g,pp))
        t+=1
        out.extend([f'def p{t} : List PartPlan := ['+', '.join(f'({lit(g)}, {glit(pp)})' for g,pp in plans)+']',f'def g{t} : List BitGroup := {glit(nxt)}',f'theorem cert{t} : ∀ gp∈p{t}, PartitionOK {L} {n} {s} {h} gp.1 gp.2 := checkPlan_sound {L} {n} {s} {h} p{t} (by decide +kernel)'])
        out.extend([f'theorem next{t} : bitNext {L} {n} {s} {h} p{t}=g{t} := by decide +kernel',f'theorem c{t} : BitCert {n} {K} {s+h} g{t} := next{t} ▸ bit_cert_next {L} {n} {K} {s} {h} p{t} (by decide) (by decide) (by decide) (by exact c{t-1}) cert{t} (by decide +kernel)'])
        s+=h; groups=nxt; print('stage',t,'s',s,'groups',len(groups),file=sys.stderr)
    assert not groups,groups
    assert s+n==K,(s,n,K)
    out.append(f'theorem result : Cert {n} {K} {s} [] := bit_cert_empty {n} {K} {s} c{t}')
    out.append('#print axioms result')
    print('\n'.join(out))
if __name__=='__main__': main(*map(int,sys.argv[1:]))
