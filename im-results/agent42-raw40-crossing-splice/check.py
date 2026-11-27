from collections import defaultdict

TABLE = '1RB0LA_1RC1RE_0RD1LA_1LD1LA_---0RF_0RB0RC'
TRANS = [None if c == '---' else (int(c[0]), 1 if c[1] == 'R' else -1, ord(c[2])-65) for r in TABLE.split('_') for c in (r[:3],r[3:])]

def family(n):
    return '0'*5+'1'*(48+21*n)+('0'+'1'*6)*(6+3*n)+'0'+'1'*5

def tape(n,head=0):
    return {head+i+1 for i,b in enumerate(family(n)) if b=='1'}

def run(t,h,q,steps):
    t=set(t); edges=defaultdict(list); counts=defaultdict(int)
    for _ in range(steps):
        move=TRANS[2*q+(h in t)]
        assert move is not None
        b,d,q=move
        if b: t.add(h)
        else: t.discard(h)
        counts[h]+=1
        edges[min(h,h+d)].append((d,q))
        h+=d
    return t,h,q,edges,counts

def insert(t,a,b):
    width=b-a
    return {x if x<=a else x+width for x in t} | {x for x in t if a<x<=b}

def main():
    t,h,q,_,_=run(set(),0,0,2340)
    assert (t,h,q)==(tape(0,-42),-42,0)
    u,h,q,edges,counts=run(tape(0),0,0,2172)
    assert (u,h,q)==(tape(1,-18),-18,0)
    cuts=[(5,26),(63,84)]
    assert 0<cuts[0][0]<cuts[0][1]<cuts[1][0]<cuts[1][1]
    for a,b in cuts: assert edges[a]==edges[b]
    ti,ui=tape(0),u
    for a,b in reversed(cuts):
        ti,ui=insert(ti,a,b),insert(ui,a,b)
    assert ti==tape(1) and ui==tape(2,-18)
    increment=sum(counts[x] for a,b in cuts for x in range(a+1,b+1))
    assert increment==702
    print('Blank entry 2340; base transition 2172; increment 702.')
    for a,b in cuts:
        print(a,b,'crossings',edges[a],'cost',sum(counts[x] for x in range(a+1,b+1)))
    print('All finite premises of the crossing-splice induction hold.')

if __name__=='__main__': main()
