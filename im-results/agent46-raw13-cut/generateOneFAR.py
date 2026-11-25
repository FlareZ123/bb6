"""Regenerate exact FAR tables from the compact DFA witnesses for raw13 D0=0RA."""
from pathlib import Path
D=Path(__file__).resolve().parent
def fmt(xs): return "["+",".join(map(str,xs))+"]"
def codes(s):
    return [24 if s[i]=="-" else 4*(ord(s[i+2])-65)+2*int(s[i])+int(s[i+1]=="R") for i in range(0,36,3)]
def compose(mask, rows):
    v=0
    while mask:
        bit=mask & -mask
        v |= rows[bit.bit_length()-1]
        mask ^= bit
    return v
def saturate(code, dfa, rev):
    d=len(dfa)//2
    N=6*d+1
    H=N-1
    halt=1<<H
    T=[0]*(2*N)
    T[H]=T[N+H]=halt
    rules=[]
    for l in range(d):
        for q in range(6):
            for a in range(2):
                x=code[2*q+a]
                i=a*N+6*l+q
                if x==24:
                    T[i]=halt
                    continue
                w,n=(x>>1)&1,x//4
                if (x&1)!=rev:
                    T[i]=1<<(6*dfa[2*l+w]+n)
                else:
                    for j in range(d):
                        for b in range(2):
                            if dfa[2*j+b]==l:
                                rules.append((i,b*N+6*j+n,w*N))
    while True:
        cur,seen=1,0
        while cur:
            seen |= cur
            assert not seen & halt
            cur=compose(cur,T)&~seen
        changed=False
        for dst,src,off in rules:
            x=T[dst]|compose(T[src],T[off:off+N])
            if x!=T[dst]:
                T[dst]=x
                changed=True
        if not changed: break
    z=halt
    while True:
        z1=z
        for i in range(N):
            if T[i]&z: z1|=1<<i
        if z==z1: break
        z=z1
    return T[:N],T[N:],z
def generate(branch):
    assert branch in ("1LA","1RA")
    prefix="1RB1LC1RC0LD1LA0RB"+branch
    module="Agent46Raw13One"+branch[1:]
    ns="BB6."+module
    proven={}
    body=["import FastFAR","import Agent46CanonicalCut","set_option maxRecDepth 100000","set_option maxHeartbeats 0","namespace "+ns,"open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut","open BB6Coverage.FAR"]
    rows=[]
    for line in (D/("one"+branch[1:]+"-dfa.txt")).read_text().splitlines():
        rev,df,*group=line.split()
        for row in group:
            i,suffix=row.split(":")
            rows.append((int(i),suffix,int(rev),df))
    for i,suffix,rev,df in sorted(rows):
        raw=prefix+suffix
        assert len(raw)==36
        dfa=list(map(int,df))
        d=len(dfa)//2
        code=codes(raw)
        m0,m1,z=saturate(code,dfa,rev)
        p=f"pF{i}"
        c=f"cF{i}"
        h=f"okF{i}"
        pp=f"(reflectPartial {p})" if rev else p
        body += [f"def {p} : PartialMachine := FAR.fromCodes {fmt(code)}",f"def {c} : Data {d} := ⟨0,{fmt(dfa)},{fmt(m0)},{fmt(m1)},{z}⟩",f"theorem {h} : ({c}).fastValid {pp} = true := by decide"]
        sound=f"({c}).sound {pp} (({c}).fastValid_sound {pp} {h})"
        proof=f"reflectNever m ({sound} (reflectTable m) (reflectCompatible {p} m hm))" if rev else f"{sound} m hm"
        body += [f"theorem neverF{i} (m : Machine) (hm : compatible {p} m) : NeverHalts m := {proof}",f"#print axioms neverF{i}"]
        assert raw not in proven
        proven[raw]=i
    assert len(proven)=={"1LA":188,"1RA":80}[branch]
    body.append("end "+ns)
    (D/(module+"FAR.lean")).write_text("\n".join(body)+"\n")
    return proven
