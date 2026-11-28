#!/usr/bin/env python3
"""Bounded exact two-sided stack-DFA invariant synthesis for Raw11 q0-148/151.

DISCOVERY ONLY: Z3 candidate models have no trusted proof status. A found
pair of push maps must be reconstructed with q0-open-automata.cjs:mitmCert,
then checked against the original-source TwoSidedAutomata Lean kernel gate.
The SMT constraints directly encode the sufficient finite closure relation;
pop edges are admitted subsets of the inverse push maps, not assumed to
be all inverse edges. This matters for precision.
"""
import argparse
import itertools
import json
import sys
import time

from z3 import And, Bool, Implies, Int, Or, Solver, sat, unsat

TABLES = {
    "148": "1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---",
    "151": "1RB1LC_1RC0RD_0LA1RD_1RB0RE_1LC1RF_---0RC",
}

def parse(code):
    raw = code.replace("_", "")
    assert len(raw) == 36, (len(raw), raw)
    tokens = [raw[i:i + 3] for i in range(0, 36, 3)]
    def item(t):
        if t == "---":
            return None
        assert t[0] in "01" and t[1] in "LR" and t[2] in "ABCDEF", t
        return (int(t[0]), t[1] == "R", ord(t[2]) - 65)
    return [item(t) for t in tokens]

def solve(code, nl, nr, timeout_ms, symmetry=True):
    """Synthesize an inductive safety relation from the source checker semantics.

    row[q,a,l,r] describes a reachable correlated control/head/stack row.
    PL[dest,b,src] and PR[dest,b,src] are allowed pop edges for left/right
    stacks. They may form a *subset* of the inverse DFA transitions, but
    every push used by an active source row forces its inverse edge.
    Every row must include *all* successors from admitted opposite pops.
    """
    table = parse(code)
    s = Solver()
    s.set(timeout=timeout_ms)
    dl = [[Int(f"L_{l}_{b}") for b in range(2)] for l in range(nl)]
    dr = [[Int(f"R_{r}_{b}") for b in range(2)] for r in range(nr)]
    for dfa, size in ((dl, nl), (dr, nr)):
        for pair in dfa:
            for dst in pair:
                s.add(dst >= 0, dst < size)
        s.add(dfa[0][0] == 0)
        if symmetry:
            for t in range(1, size):
                s.add(Or(*(dfa[i][b] == t for i in range(t) for b in range(2))))

    pl = [[[Bool(f"PL_{j}_{b}_{i}") for i in range(nl)] for b in range(2)]
          for j in range(nl)]
    pr = [[[Bool(f"PR_{j}_{b}_{i}") for i in range(nr)] for b in range(2)]
          for j in range(nr)]
    row = [[[[Bool(f"Q_{q}_{a}_{l}_{r}") for r in range(nr)]
             for l in range(nl)] for a in range(2)] for q in range(6)]
    s.add(pl[0][0][0], pr[0][0][0], row[0][0][0][0])
    for size, pop, dfa in ((nl, pl, dl), (nr, pr, dr)):
        for dest in range(size):
            for b in range(2):
                for src in range(size):
                    s.add(Implies(pop[dest][b][src], dfa[src][b] == dest))

    for q, a, l, r in itertools.product(range(6), range(2), range(nl), range(nr)):
        active = row[q][a][l][r]
        rule = table[2*q+a]
        if rule is None:
            s.add(~active)
            continue
        w, move_right, next_q = rule
        if move_right:
            for j in range(nl):
                trans = And(active, dl[l][w] == j)
                s.add(Implies(trans, pl[j][w][l]))
                for b in range(2):
                    for r0 in range(nr):
                        s.add(Implies(And(trans, pr[r][b][r0]),
                                      row[next_q][b][j][r0]))
        else:
            for j in range(nr):
                trans = And(active, dr[r][w] == j)
                s.add(Implies(trans, pr[j][w][r]))
                for b in range(2):
                    for l0 in range(nl):
                        s.add(Implies(And(trans, pl[l][b][l0]),
                                      row[next_q][b][l0][j]))
    started = time.monotonic()
    verdict = s.check()
    duration = round(time.monotonic()-started, 3)
    if verdict != sat:
        return {"status": "unsat" if verdict == unsat else "unknown",
                "reason": s.reason_unknown() if verdict != unsat else "",
                "left_states": nl, "right_states": nr, "seconds": duration}
    model = s.model()
    L = [[model.eval(dl[i][b], model_completion=True).as_long() for b in range(2)]
         for i in range(nl)]
    R = [[model.eval(dr[i][b], model_completion=True).as_long() for b in range(2)]
         for i in range(nr)]
    return {"status": "sat", "left_states": nl, "right_states": nr,
            "seconds": duration, "left": L, "right": R,
            "rows": sum(bool(model.eval(row[q][a][l][r]))
                        for q,a,l,r in itertools.product(range(6),range(2),range(nl),range(nr)))}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("case", choices=TABLES)
    p.add_argument("--min-states", type=int, default=2)
    p.add_argument("--max-states", type=int, default=5)
    p.add_argument("--timeout-ms", type=int, default=25000)
    p.add_argument("--budget-seconds", type=int, default=450)
    p.add_argument("--output", required=True)
    p.add_argument("--no-symmetry", action="store_true")
    args = p.parse_args()
    assert 1 <= args.min_states <= args.max_states <= 12
    assert args.budget_seconds > 0 and args.timeout_ms > 0
    code = TABLES[args.case]
    pairs = [(l,r) for l in range(args.min_states, args.max_states+1)
             for r in range(args.min_states, args.max_states+1)]
    pairs.sort(key=lambda t:(t[0]+t[1], t[0]*t[1], abs(t[0]-t[1])))
    deadline = time.monotonic()+args.budget_seconds
    records = []
    for nl,nr in pairs:
        remain = int((deadline-time.monotonic())*1000)
        if remain < 1000:
            break
        record = solve(code,nl,nr,min(remain,args.timeout_ms),
                       symmetry=not args.no_symmetry)
        records.append(record)
        print(json.dumps({"case": args.case, **record}), flush=True)
        if record["status"] == "sat":
            output = {"table":code, "case":args.case,
                      "synthesis":"untrusted Z3 model; MUST reconstruct and kernel-check",
                      "left":record["left"],"right":record["right"],
                      "trials":records}
            with open(args.output,"w") as out:
                json.dump(output,out,indent=2)
                out.write("\n")
            return 0
    with open(args.output,"w") as out:
        json.dump({"table":code,"case":args.case,"trials":records,
                   "certificate":None},out,indent=2)
        out.write("\n")
    return 0

if __name__ == "__main__":
    sys.exit(main())
