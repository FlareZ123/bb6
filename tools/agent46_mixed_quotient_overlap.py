"""Independent exact B8/M32 quotient audit of Agent46's eight high cylinders.

Finite computation only: abstract reachability never proves real-machine reachability.
The original-source Lean proofs are in im-results/agent46-c-mixed*.
"""
from collections import deque

BASE, MOD, N = 8, 32, 40

def q(x):
    return x if x < BASE else BASE + (x - BASE) % MOD

def code(a,k,c):
    return (a*N+k)*N+c

def nxt(a,k,c):
    if c == 1:
        return a,k+1,0
    if c == 2:
        return None
    if c == 3:
        return a,k+2,1
    if c == 0:
        if a == 0:
            return 1,0,2*k+2
        if a == 1:
            return (5,0,1) if k == 0 else (2,2,2*k-1)
        return a-2,1,2*k+1
    if a == 0:
        return (2*k+2,2,c-3) if k%2==0 else (2*k+3,0,c)
    return a-1,k+1,c-1

def old_graph():
    seen=bytearray(N**3)
    start=code(5,0,1)
    seen[start]=1
    queue=deque([start])
    edges=0
    while queue:
        i=queue.popleft()
        a,k,c=i//1600,(i//40)%40,i%40
        for aa in (a,a+MOD) if a>=BASE else (a,):
            for kk in (k,k+MOD) if k>=BASE else (k,):
                for cc in (c,c+MOD) if c>=BASE else (c,):
                    t=nxt(aa,kk,cc)
                    if t is None:
                        continue
                    edges+=1
                    jj=code(*map(q,t))
                    if not seen[jj]:
                        seen[jj]=1
                        queue.append(jj)
    assert sum(seen)==31570 and edges==189834
    return seen

def main():
    seen=old_graph()
    for k in (10,142,115,355):
        assert seen[code(q(1),q(k),q(0))]
        print(f'First gate (1,{k},0) survives earlier B8/M32 abstraction')
    groups=[
        ('C38',[(95,6),(191,38)]),
        ('C58',[(95,26),(191,58)]),
        ('C3',[(191,67),(383,3)]),
        ('C51',[(191,115),(383,51)]),
    ]
    for group,pairs in groups:
        for j,m in pairs:
            assert m>=2
            k=2**(2*m+2)*(j+3)-j-3*m-5
            assert k>=0
            a=2*j+3
            assert seen[code(q(a),q(k),q(0))]
            print(f'{group} high gateway (j,m)=({j},{m}) survives earlier B8/M32 abstraction')
    print('PASS: all twelve representative targets are quotient-reachable; none is an actual reachability witness.')

if __name__=='__main__':
    main()
