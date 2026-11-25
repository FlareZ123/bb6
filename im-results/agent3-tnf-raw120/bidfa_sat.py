"""Untrusted finite BiDFA synthesis for raw120 holdouts.

The DFA tables are the only solver outputs that matter. bidfa_emit recomputes
the least closure; BiDFA.lean independently checks the resulting certificate.
"""
from itertools import product
import json
import sys
import time
import z3

def solve(table, nl, nr, timeout=10000):
    p=[table.replace("_","")[i:i+3] for i in range(0,36,3)]
    z=z3.SolverFor("QF_FD")
    z.set(timeout=timeout)
    sizes=(nl,nr)
    D=[[[z3.Bool(f"d{side}_{i}_{j}") for j in range(n)] for i in range(2*n)] for side,n in enumerate(sizes)]
    E=[[[[z3.Bool(f"e{side}_{i}_{b}_{j}") for j in range(n)] for b in range(2)] for i in range(n)] for side,n in enumerate(sizes)]
    S=[[[z3.Bool(f"s{slot}_{l}_{r}") for r in range(nr)] for l in range(nl)] for slot in range(12)]
    for side,n in enumerate(sizes):
        z.add(D[side][0][0],E[side][0][0][0])
        for i,row in enumerate(D[side]):
            z.add(z3.PbEq([(x,1) for x in row],1))
            for j in range(i+1,n):z.add(z3.Not(row[j]))
            for j in range(2,min(i+1,n)):
                z.add(z3.Implies(row[j],z3.Or([D[side][k][j-1] for k in range(i)])))
        for i,b,j in product(range(n),range(2),range(n)):
            z.add(z3.Implies(E[side][i][b][j],D[side][2*j+b][i]))
    z.add(S[0][0][0])
    for slot,l,r in product(range(12),range(nl),range(nr)):
        v=S[slot][l][r];t=p[slot]
        if t=="---":
            z.add(z3.Not(v));continue
        w=int(t[0]);q=ord(t[2])-65
        if t[1]=="R":
            for dest in range(nl):
                d=D[0][2*l+w][dest]
                z.add(z3.Or(z3.Not(v),z3.Not(d),E[0][dest][w][l]))
                for b,j in product(range(2),range(nr)):
                    z.add(z3.Or(z3.Not(v),z3.Not(d),z3.Not(E[1][r][b][j]),S[2*q+b][dest][j]))
        else:
            for dest in range(nr):
                d=D[1][2*r+w][dest]
                z.add(z3.Or(z3.Not(v),z3.Not(d),E[1][dest][w][r]))
                for b,j in product(range(2),range(nl)):
                    z.add(z3.Or(z3.Not(v),z3.Not(d),z3.Not(E[0][l][b][j]),S[2*q+b][j][dest]))
    res=z.check()
    if res!=z3.sat:return None
    m=z.model()
    return [[next(j for j,x in enumerate(row) if z3.is_true(m.eval(x,model_completion=True))) for row in d] for d in D]

def search(table,max_total=15,timeout=10000):
    for total in range(2,max_total+1):
        pairs=sorted(((l,total-l) for l in range(1,total) if max(l,total-l)<=10),key=lambda x:abs(x[0]-x[1]))
        for l,r in pairs:
            ans=solve(table,l,r,timeout)
            if ans:return ans
    return None

if __name__=="__main__":
    # Input JSON object: index -> machine. Results are printed as each is found.
    tables=json.load(open(sys.argv[1]))
    result={}
    for idx,table in tables.items():
        start=time.monotonic()
        ans=search(table,int(sys.argv[2]) if len(sys.argv)>2 else 15)
        print(json.dumps({"index":idx,"table":table,"dfas":ans,"seconds":round(time.monotonic()-start,1)}),flush=True)
        if ans:result[idx]=[table,*ans]
    print("BIDFA_RESULT "+json.dumps(result,sort_keys=True),flush=True)
