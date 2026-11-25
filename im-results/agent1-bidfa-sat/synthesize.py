#!/usr/bin/env python3
"""Synthesize bounded two-sided stack summaries by a factored Boolean SAT encoding."""
from itertools import combinations, product
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import ctypes as C
import ctypes.util
import hashlib
import json
import re
import sys
import time

HERE = Path(__file__).resolve().parent
IM = HERE.parent
A16 = IM / "agent16-raw118"
A40 = IM / "agent40-raw118-independent"

def formula(table, L, R):
    rows = table.replace('_', '')
    assert len(rows) == 36 and 1 <= L <= 64 and 1 <= R <= 64
    moves = [rows[i:i+3] for i in range(0,36,3)]
    out = []
    def declare(v):
        out.append(f"(declare-fun {v} () Bool)")
        return v
    def clause(*lits):
        out.append("(assert (or " + " ".join(lits) + "))")
    def neg(v):
        return "(not " + v + ")"
    d = [[[[declare(f"d{s}_{i}_{b}_{j}") for j in range(N)]
            for b in range(2)] for i in range(N)]
         for s,N in enumerate((L,R))]
    e = [[[declare(f"e{s}_{i}_{b}") for b in range(2)]
          for i in range(N)] for s,N in enumerate((L,R))]
    reach = [[[[declare(f"r{q}_{a}_{l}_{r}") for r in range(R)]
               for l in range(L)] for a in range(2)] for q in range(6)]
    push = [[[[declare(f"p{s}_{q}_{l}_{r}") for r in range(R)]
              for l in range(L)] for q in range(6)] for s in range(2)]
    for s,N in enumerate((L,R)):
        flat = [d[s][i][b] for i in range(N) for b in range(2)]
        for k,choices in enumerate(flat):
            clause(*choices)
            for a,b in combinations(choices,2):
                clause(neg(a),neg(b))
            # Number reachable DFA states by first discovery in BFS order;
            # pad unreachable states with transitions to zero.
            for j in range(2,N):
                clause(neg(choices[j]),*(flat[h][j-1] for h in range(k)))
    clause(reach[0][0][0][0])
    for q,a,l,r in product(range(6),range(2),range(L),range(R)):
        x = reach[q][a][l][r]
        m = moves[2*q+a]
        if m in ('---','HHH'):
            clause(neg(x))
            continue
        w, dr, n = int(m[0]),m[1],ord(m[2])-65
        assert dr in 'LR' and 0 <= n < 6
        if dr == 'R':
            clause(neg(x),e[0][l][w])
            for j in range(L):
                clause(neg(x),neg(d[0][l][w][j]),push[0][n][j][r])
        else:
            clause(neg(x),e[1][r][w])
            for j in range(R):
                clause(neg(x),neg(d[1][r][w][j]),push[1][n][l][j])
    for n,l,r in product(range(6),range(L),range(R)):
        x = push[0][n][l][r]
        if r == 0:
            clause(neg(x),reach[n][0][l][0]) # implicit infinite blank edge
        for b,j in product(range(2),range(R)):
            clause(neg(x),neg(e[1][j][b]),neg(d[1][j][b][r]),reach[n][b][l][j])
        x = push[1][n][l][r]
        if l == 0:
            clause(neg(x),reach[n][0][0][r])
        for b,j in product(range(2),range(L)):
            clause(neg(x),neg(e[0][j][b]),neg(d[0][j][b][l]),reach[n][b][j][r])
    return "\n".join(out), d

def solve(table,L,R,timeout_ms=5000):
    source,d = formula(table,L,R)
    dll = ctypes.util.find_library("z3")
    if not dll:
        raise RuntimeError("libz3 is required (Ubuntu: libz3-4)")
    lib=C.CDLL(dll)
    P=C.c_void_p
    def bind(name,result,*args):
        f=getattr(lib,name); f.restype=result;f.argtypes=args
        return f
    mkcfg=bind('Z3_mk_config',P)
    setcfg=bind('Z3_set_param_value',None,P,C.c_char_p,C.c_char_p)
    mkctx=bind('Z3_mk_context',P,P)
    delcfg=bind('Z3_del_config',None,P)
    delctx=bind('Z3_del_context',None,P)
    mk=bind('Z3_mk_solver',P,P)
    inc=bind('Z3_solver_inc_ref',None,P,P)
    dec=bind('Z3_solver_dec_ref',None,P,P)
    load=bind('Z3_solver_from_string',None,P,P,C.c_char_p)
    check=bind('Z3_solver_check',C.c_int,P,P)
    model=bind('Z3_solver_get_model',P,P,P)
    mstr=bind('Z3_model_to_string',C.c_char_p,P,P)
    cfg=mkcfg()
    setcfg(cfg,b"timeout",str(timeout_ms).encode())
    ctx=mkctx(cfg);delcfg(cfg)
    solver=mk(ctx);inc(ctx,solver)
    try:
        load(ctx,solver,source.encode())
        status=check(ctx,solver)
        if status != 1:
            return ("unsat" if status == -1 else "unknown"), None
        values=set(re.findall(r"(?m)^([A-Za-z0-9_]+) -> true$",mstr(ctx,model(ctx,solver)).decode()))
        ans=[]
        for side in d:
            dest=[]
            for choices_by_symbol in side:
                for choices in choices_by_symbol:
                    selected=[j for j,v in enumerate(choices) if v in values]
                    assert len(selected)==1, choices
                    dest.append(selected[0])
            ans.append(dest)
        return "sat",ans
    finally:
        dec(ctx,solver);delctx(ctx)

def prepare(work, target_file):
    """Consume the exact known partition without rerunning the BiDFA bank."""
    sys.path.insert(0,str(A16))
    sys.path.insert(0,str(A40))
    from bidfa_emit import EXAMPLES as old
    from tree_emit import EXAMPLES as tree
    from independent import ROWS as independent
    from generate_recursive_counter import CASES as rec1
    from generate_recursive_more import CASES as rec2
    sys.path.insert(0,str(IM/"agent31-three-hole-tnf"))
    sys.path.insert(0,str(IM/"agent47-raw114-cut"))
    from generate_symbolic import SINGLE, MULTI
    data=(work/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()=="00b82e8ded916fb719ebfd627d29da4bbf86659039b3b7889ff60a3f9ae396f9"
    rows=data.decode().splitlines()
    hard=set(json.loads((work/"candidates.json").read_text())["hard"])
    groups=[set(SINGLE)|set(MULTI),set(independent),
      {int(x.split()[0]) for x in (A40/"phase_candidates.tsv").read_text().splitlines() if x.strip()},
      {int(x[0]) for x in rec1+rec2},{int(x[0]) for x in old},{int(x[0]) for x in tree}]
    known=set().union(*groups)
    assert len(rows)==6085 and len(hard)==274 and len(known)==187
    assert sum(map(len,groups))==len(known) and known<=hard
    targets=[(i,rows[i]) for i in sorted(hard-known)]
    assert len(targets)==87 and all(t.count("---")==1 for _,t in targets)
    target_file.parent.mkdir(parents=True,exist_ok=True)
    target_file.write_text("".join(f"{i}\t{t}\n" for i,t in targets))
    print("Exact target roster",len(targets),hashlib.sha256(target_file.read_bytes()).hexdigest(),flush=True)

# No prior DFA bank search. Independently synthesize at these state budgets.
SCHEDULE=[(6,6,2000),(8,8,3000),(10,10,5000),(8,12,5000),
          (12,8,5000),(12,12,8000),(16,16,15000)]

def solve_row(entry):
    i,table=entry
    trace=[]
    for L,R,ms in SCHEDULE:
        start=time.monotonic()
        status,d=solve(table,L,R,ms)
        trace.append({"left":L,"right":R,"status":status,"seconds":round(time.monotonic()-start,3)})
        if d is not None:
            return {"index":i,"table":table,"left":d[0],"right":d[1],"attempts":trace}
    return {"index":i,"table":table,"attempts":trace}

def search(target_file,workers,out):
    sys.path.insert(0,str(A16))
    from tree_emit import emit
    from bidfa_emit import witness
    targets=[(int(i),t) for i,t in (x.split() for x in target_file.read_text().splitlines())]
    out.mkdir(parents=True,exist_ok=True)
    hits=[]; attempts=[]
    header=("import TreeBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
      "namespace BB6Coverage.Agent1BiDFASat.Raw118\nopen BB6Coverage Agent16BiDFA.TreeCheck\n")
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for result in pool.map(solve_row,targets):
            attempts.append(result)
            i,table=result["index"],result["table"]
            if "left" not in result:
                print("UNRESOLVED",i,result["attempts"],flush=True)
                continue
            # Existing independent closure generator and Lean emitter.
            dl,dr=result["left"],result["right"]
            e,states=witness(table,dl,dr)
            code,n,m=emit(i,table,dl,dr)
            assert n==len(states) and m==sum(map(len,e))
            result.update(states=n,edges=m)
            hits.append(result)
            (out/f"Raw118Sat{i}.lean").write_text(header+code+"\nend BB6Coverage.Agent1BiDFASat.Raw118\n")
            (out/"hits.json").write_text(json.dumps(hits,indent=2)+"\n")
            print("HIT",i,table,dl,dr,n,m,flush=True)
    (out/"hits.json").write_text(json.dumps(hits,indent=2)+"\n")
    (out/"attempts.json").write_text(json.dumps(attempts,indent=2)+"\n")
    print("SAT candidate leaves",len(hits),"of",len(targets),flush=True)

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser()
    sub=ap.add_subparsers(dest="cmd",required=True)
    s=sub.add_parser("single")
    s.add_argument("table");s.add_argument("left",type=int);s.add_argument("right",type=int)
    s.add_argument("--timeout-ms",type=int,default=5000)
    p=sub.add_parser("prepare");p.add_argument("work",type=Path);p.add_argument("targets",type=Path)
    b=sub.add_parser("search");b.add_argument("targets",type=Path);b.add_argument("--workers",type=int,default=4);b.add_argument("--out",type=Path,required=True)
    args=ap.parse_args()
    if args.cmd=="single":
        print(solve(args.table,args.left,args.right,args.timeout_ms))
    elif args.cmd=="prepare":
        prepare(args.work,args.targets)
    else:
        search(args.targets,args.workers,args.out)
