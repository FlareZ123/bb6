"""Independently generate and audit a P-automaton safety certificate.
No simulation cutoff is used in the proof check. Python 3.10+, stdlib only.
"""
import json
import sys
from pathlib import Path

def check_graph(graph):
    heads=graph['head']; delta=[dict(row) for row in graph['delta']]; n=len(heads)
    assert len(delta)==n and heads[0]==0 and all(type(a)==int and 0<=a<=12 for a in heads)
    inv=[set() for _ in heads]; inv[0].add(0)
    for i,row in enumerate(delta):
        assert len(row)==len(graph['delta'][i])
        for a,j in row.items():
            assert 0<=j<n and j!=0 and heads[j]==a and not (i==0 and a==0)
            inv[j].add(i)
    assert all(inv)
    return heads,delta,inv

def build(graph,T=13):
    heads,delta,inv=check_graph(graph);n=len(heads);U=7*n;END=T+4;A=END+1
    assert T>=4
    def cls(v):return v if v<T else T+v%4
    def images(c,d):
        if c<T:return (cls(c+d),)
        base=T+(c-T-T%4)%4
        assert base+d>=0 and d>=-4
        return tuple(sorted({cls(base+d),cls(base+4+d)}))
    def push(i,*word):
        for a in reversed(word):
            if i==0 and a==0:continue
            if i<0 or a not in delta[i]:return -1
            i=delta[i][a]
        return i
    rules=set();bad=set()
    def rule(p,x,q,w=()):
        if q<0:bad.add((p,x))
        else:rules.add((p,x,q,tuple(w)))
    for l,a in enumerate(heads):
        main,inc,s2,s20,s3,s3n,s30=(k*n+l for k in range(7))
        bad.add((main,0))
        if a<2:bad.add((main,1))
        else:
            for t in inv[l]:
                q=push(t,2,a-2);rule(main,1,n+q if q>=0 else -1)
        rule(main,2,s2);rule(main,3,s3)
        for t in inv[l]:
            rule(main,END,t,(cls(a+2),1,END))
            for x in range(4,END):
                for y in images(x,-4):rule(main,x,t,(cls(a+2),1,y))
        for x in range(A):
            for y in ((END,) if x==END else images(x,1)):rule(inc,x,main,(y,))
            if x==0:rule(s2,x,s20)
            else:
                for t in inv[l]:rule(s2,x,push(t,a+3),(x,))
            for t in inv[l]:
                for y in ((END,) if x==END else images(x,a+5)):rule(s20,x,t,(y,))
            if x==1:rule(s3,x,s3n)
            else:bad.add((s3,x))
            for t in inv[l]:
                if x==0:
                    q=push(t,0,a+2);rule(s3n,x,6*n+q if q>=0 else -1)
                else:rule(s3n,x,push(t,2,0,a+2),(x,))
            for y in ((END,) if x==END else images(x,4)):rule(s30,x,main,(y,))
    return sorted(rules),bad,U,A

def saturate(rules,bad,U,A):
    e=[0]*((U+1)*A);end=1<<U
    for p,x in bad:e[p*A+x]|=end
    for x in range(A):e[U*A+x]=end
    def dest(q,w):
        s=1<<q
        for x in w:
            t=0
            while s:
                k=s&-s;s-=k;t|=e[(k.bit_length()-1)*A+x]
            s=t
        return s
    rounds=0
    while True:
        changed=False;rounds+=1
        for p,x,q,w in rules:
            i=p*A+x;v=e[i]|dest(q,w)
            if v!=e[i]:e[i]=v;changed=True
        if not changed:break
    # A separate closure audit: soundness needs closure, not leastness.
    assert all(e[p*A+x]&end for p,x in bad)
    assert all(e[U*A+x]&end for x in range(A))
    assert all(dest(q,w)&~e[p*A+x]==0 for p,x,q,w in rules)
    safe=not (e[A-1]&end)
    return safe,e,rounds

if __name__=='__main__':
    g=json.load(open(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('graph.json')))
    T=13
    rules,bad,U,A=build(g,T);safe,e,rounds=saturate(rules,bad,U,A)
    report=dict(T=T,left=len(g['head']),states=U+1,alphabet=A,rules=len(rules),bad=len(bad),edges=sum(v.bit_count() for v in e),rounds=rounds,safe=safe)
    print(report)
    assert report==dict(T=13,left=378,states=2647,alphabet=18,rules=33882,bad=17887,edges=58790,rounds=28,safe=True)
    if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps({'T':T,'U':U,'A':A,'edges':[hex(v) for v in e]},separators=(',',':')))
