"""Reproduce the raw120 sparse FAR comparison with a pinned 24-leaf sample.

Run from an output directory with WeakFAR, SparseFAR and the original FastFAR
dependency closure already compiled using Lean 4.36.0-rc2 and LEAN_PATH.
"""
from itertools import product
from pathlib import Path
import subprocess
from time import monotonic

SAMPLE = """
613 1RB0RF_1RC---_0RD0RA_1LD1RE_1LB1LE_0LC0RC 10ad41c974f1g52g95ebdd67d58475ab59b
614 1RB0RF_1RC---_0RD0RA_1LD1RE_1LB1LE_1LD0RC 10ad41c974f1g52g95ebdd67d58475ab59b
1781 1RB1RC_1RC1RA_0RD0RF_1LD1RE_1LB1LE_---1LA 10ad41c974f1g52g95ebdd67d58475ab59b
1985 1RB1RC_1RC1LE_0RD0RF_1LD1RE_1LB1LE_---1RA 10ad41c974f1g52g95ebdd67d58475ab59b
1986 1RB1RC_1RC1RB_0RD0RF_1LD1RE_1LB1LE_---1RA 10ad41c974f1g52g95ebdd67d58475ab59b
1987 1RB1RC_1RC1RD_0RD0RF_1LD1RE_1LB1LE_---1RA 10ad41c974f1g52g95ebdd67d58475ab59b
1988 1RB1RC_1RC1RE_0RD0RF_1LD1RE_1LB1LE_---1RA 10ad41c974f1g52g95ebdd67d58475ab59b
2383 1RB0RC_1RC1RF_0RD1LA_1LD1RE_1LB1LE_---1RA 10ad41c974f1g52g95ebdd67d58475ab59b
1258 1RB---_1RC1RE_0RD0RF_1LD1RE_1LB1LE_1LE0LA 00102030401
1927 1RB---_1RC0RD_0RD0RF_1LD1RE_1LB1LE_1RC1LF 00102030400
1268 1RB---_1RC0RE_0RD0RF_1LD1RE_1LB1LE_1RA0LA 00102030401
4341 1RB---_1RC---_0RD1RF_1LD1RE_1LB1LE_1RD1RF 00121334444
3239 1RB1RA_1RC0LF_0RD1RB_1LD1RE_1LB1LE_---1LA 10121343333
128 1RB0RF_1RC1RA_0RD0LB_1LD1RE_1LB1LE_---1LB 009491187778731588756
535 1RB0LF_1RC1RE_0RD0RA_1LD1RE_1LB1LE_0RE--- 00102030401
1332 1RB1RA_1RC1RA_0RD0RF_1LD1RE_1LB1LE_---0LB 00102030400
354 1RB---_1RC0RC_0RD0LF_1LD1RE_1LB1LE_0RC1RA 00102030400
2502 1RB1RA_1RC0RA_0RD1LB_1LD1RE_1LB1LE_------ 00102030400
258 1RB---_1RC1RF_0RD0LD_1LD1RE_1LB1LE_0RC1RF 00102030400
2240 1RB---_1RC1LC_0RD0RF_1LD1RE_1LB1LE_0RC1RF 00102030400
3925 1RB---_1RC1LE_0RD1RF_1LD1RE_1LB1LE_1RE0RC 00102030400
3220 1RB---_1RC0LF_0RD1RB_1LD1RE_1LB1LE_0RB0LD 00102030400
3543 1RB1RF_1RC---_0RD1RF_1LD1RE_1LB1LE_1RC0LA 00121334444
3280 1RB1RA_1RC0RF_0RD1RB_1LD1RE_1LB1LE_---0RA 00102030401
""".strip().splitlines()

def masks(p,rev,dfa):
    d=len(dfa)//2
    N=6*d+1
    H=N-1
    halt=1<<H
    T=[0]*(2*N)
    T[H]=T[N+H]=halt
    rules=[]
    for l,q,a in product(range(d),range(6),range(2)):
        mv=p[2*q+a]
        dst=a*N+6*l+q
        if mv=="---":
            T[dst]=halt
            continue
        w=int(mv[0])
        r=int(mv[1]=="R")
        nxt=ord(mv[2])-65
        if r!=rev:
            T[dst]=1<<(6*dfa[2*l+w]+nxt)
        else:
            for j,b in product(range(d),range(2)):
                if dfa[2*j+b]==l:
                    rules.append((dst,b*N+6*j+nxt,w*N))
    while True:
        z=halt
        while True:
            zz=z
            for j in range(N):
                if T[j]&z: z|=1<<j
            if z==zz: break
        assert not z&1
        changed=False
        for dst,src,off in rules:
            v=T[dst]
            bits=T[src]
            while bits:
                b=bits&-bits
                v|=T[off+b.bit_length()-1]
                bits^=b
            if v!=T[dst]:
                T[dst]=v
                changed=True
        if not changed: return d,dfa,T[:N],T[N:],z

def bitcodes(x):
    return [i for i in range(x.bit_length()) if (x>>i)&1]

def boolean(x):
    return str(bool(x)).lower()

def generate(mode):
    # All variants use the same direct table and exact FAR masks.
    lines=["import SparseFAR", "set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0", "set_option exponentiation.threshold 4096",
           "open BB6Coverage BB6Coverage.FAR"]
    for i,line in enumerate(SAMPLE):
        _,code,mask=line.split()
        code=code.replace("_","")
        rows=[code[j:j+3] for j in range(0,36,3)]
        d,D,L,R,z=masks(rows,int(mask[0]),[int(x,36) for x in mask[1:]])
        lines.append(f"def t{i} : PartialMachine := fun s => match s.1.val,s.2 with")
        for j,mv in enumerate(rows):
            if mv!="---":
                lines.append(f"  | {j//2},{boolean(j%2)} => some (some ⟨{boolean(mv[0]=='1')},{boolean(mv[1]=='R')},{ord(mv[2])-65}⟩)")
        lines.append("  | _,_ => none")
        lines.append(f"def f{i} : Data {d} := ⟨0,{D},{L},{R},{z}⟩")
        arg=f"(reflectPartial t{i})" if mask[0]=="1" else f"t{i}"
        if mode=="Fast":
            check=f"f{i}.fastValid {arg}"
        elif mode=="Weak":
            check=f"Weak.check f{i} {arg}"
        else:
            lines.append(f"def s{i} : Sparse.Rows := ⟨{[bitcodes(x) for x in L]},{[bitcodes(x) for x in R]}⟩")
            check=f"Sparse.check f{i} s{i} {arg}"
        lines.append(f"theorem c{i} : {check} = true := by decide")
    name=f"Benchmark{mode}"
    Path(name+".lean").write_text("\n".join(lines)+"\n")
    return name

if __name__=="__main__":
    for mode in ("Fast","Weak","Sparse"):
        name=generate(mode)
        t=monotonic()
        subprocess.run(["lean","-o",name+".olean",name+".lean"],check=True)
        print(mode, round(monotonic()-t,3), "seconds",flush=True)
