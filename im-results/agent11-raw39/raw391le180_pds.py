"""Finite left-abstraction / exact right-stack safety checker for Raw39 1LE180.
No finite state abstraction is asserted to succeed. Saturation over finite controls
is exact for the abstract pushdown system; rejecting all padded blanks is sufficient
for concrete nonhalting. Run with a suffix length (default 3).
"""
from collections import deque
RULES=[("0000","1011",2),("0001","1100",4),("00100","10111",2),
("00101","11000",5),("00110","11011",3),("00111","11100",5),
("01000","10111",2),("01001","11000",5),("01010","11011",3),
("01011","11100",5)]
def suffix_dfa(k):
    mask=(1<<k)-1
    return [[(2*i+b)&mask for b in range(2)] for i in range(1<<k)]

def pds(L,allowed=None):
    n=len(L); rules=[]; ctrl=2*n
    def run(l,w):
        for b in w:
            l=L[l][int(b)]
            if l<0: return -1
        return l
    def add(p,b,q,w):
        if p>=0 and q>=0: rules.append((p,int(b),q,w))
    for l in range(n):
        if allowed is None or l in allowed:
            trie={'':l}
            for u,v,h in RULES:
                dest=run(l,v[:h])
                if dest<0: continue
                s=''
                for i,b in enumerate(u):
                    p=trie[s]; s+=b
                    if i==len(u)-1: add(p,b,dest,v[h:])
                    elif s not in trie:
                        trie[s]=ctrl;ctrl+=1;add(p,b,trie[s],'')
        add(l,1,n+l,'1')
        p=run(l,'1')
        if p>=0:
            for b in '01': add(n+p,b,n+l,'0'+b)
        for a in '01':
            p=run(l,a+'0')
            if p>=0 and (a=='1' or allowed is None or l in allowed):
                for b in '01': add(n+p,b,l,a+'0'+b)
    B1,B2,B3=ctrl,ctrl+1,ctrl+2
    edges=[[set() for _ in range(ctrl+3)] for _ in range(2)]
    for l in range(n):
        if allowed is None or l in allowed: edges[0][l].add(B1)
    edges[1][B1].add(B2);edges[1][B2].add(B3)
    for b in range(2): edges[b][B3].add(B3)
    return rules,edges,B3

def certify(L,allowed=None):
    assert L[0][0]==0
    rules,E,B=pds(L,allowed)
    def bad_blank():
        seen={0};q=deque([0])
        while q:
            p=q.popleft()
            if p==B:return True
            for s in E[0][p]-seen:
                seen.add(s);q.append(s)
        return False
    rounds=0
    while True:
        rounds+=1;change=False
        for p,b,q,w in rules:
            S={q}
            for a in w:
                S={t for s in S for t in E[int(a)][s]}
                if not S: break
            new=S-E[b][p]
            if new:E[b][p].update(new);change=True
        if bad_blank():return False,rounds,sum(len(s) for row in E for s in row)
        if not change:return True,rounds,sum(len(s) for row in E for s in row)

# Invariant on normalized physical left words:
# all internal one-runs length >=2, zeros length <=3;
# a final singleton may be followed by <=1 zero, only at A1.
SHAPE=[[0,1],[3,2],[4,2],[-1,-1],[5,1],[6,1],[-1,1]]
A0={0,2,4,5,6}
def product_suffix(k):
    S=suffix_dfa(k);states=[(0,0)];ids={states[0]:0};rows=[]
    for a,b in states:
        row=[]
        for x in range(2):
            c=SHAPE[a][x]
            if c<0:row.append(-1);continue
            st=(c,S[b][x])
            if st not in ids:ids[st]=len(states);states.append(st)
            row.append(ids[st])
        rows.append(row)
    return rows,{i for i,(a,b) in enumerate(states) if a in A0}

if __name__=='__main__':
    import sys
    k=int(sys.argv[1]) if len(sys.argv)>1 else 3
    L,A=product_suffix(k)
    print("shape x suffix",k,"states",len(L),"safe,rounds,edges",certify(L,A))
