"""Generate a finite two-sided block-grammar Lean certificate candidate for Raw56 residual M39232.

The parameters were found by targeted asymmetric periodic-block search. The emitted
source is intended for the same kernel-checked sharding pipeline used for M42763.
"""
from collections import defaultdict
from pathlib import Path
import argparse, sys

TABLE = "1RB1RA_1RC0LB_0RD1RF_1LD1LE_0RC1LB_---0RA"
LEFT = (23, (4, 6), 4, 1)
RIGHT = (24, (4, 6), 4, 2)
EXPECTED = (19013, 141, 933)

HERE = Path(__file__).resolve()
AUTOMATA = HERE.parent.parent / "agent4-two-sided-automata"
sys.path.insert(0, str(AUTOMATA))
from emit_automata import emit

def blockgram(params):
    k, periods, c, m = params
    def push(s, b):
        w = str(int(b)) + s
        changed = True
        while changed:
            changed = False
            for i in range(len(w)):
                for period in periods:
                    end = i + period * (c + m)
                    if end <= len(w) and w[i:i+period] * (c + m) == w[i:end]:
                        w = w[:i] + w[i + m*period:]
                        changed = True
                        break
                if changed:
                    break
        return w[:k].rstrip("0")
    return push

def abstract(p, pushL, pushR, limit=21000):
    P = [pushL, pushR]
    tab = [[""], [""]]
    ids = [{"": 0}, {"": 0}]
    D = [{}, {}]
    def dfa(d, i, b):
        key = (i, b)
        if key in D[d]:
            return D[d][key]
        y = P[d](tab[d][i], b)
        j = ids[d].get(y)
        if j is None:
            j = len(tab[d]); tab[d].append(y); ids[d][y] = j
        D[d][key] = j
        return j
    edges = [defaultdict(set), defaultdict(set)]
    wait = [defaultdict(list), defaultdict(list)]
    for e in edges: e[0].add((0, 0))
    seen = {(0, 0, 0, 0)}
    todo = [(0, 0, 0, 0)]
    failure = False
    def add(x):
        nonlocal failure
        if x not in seen:
            seen.add(x); todo.append(x)
            if p[2*x[0] + x[1]] == "---": failure = True
            if len(todo) >= limit: raise RuntimeError("certificate state cap reached")
    def pop(x, edge, pushed):
        q, b, l, r = x
        mv = p[2*q + b]
        ns = ord(mv[2]) - 65
        c, pre = edge
        add((ns, c, pushed, pre) if mv[1] == "R" else (ns, c, pre, pushed))
    def add_edge(d, j, b, pre):
        edge = (b, pre)
        if edge in edges[d][j]: return
        edges[d][j].add(edge)
        for cfg, pushed in wait[d][j]: pop(cfg, edge, pushed)
    i = 0
    while i < len(todo) and not failure:
        cfg = todo[i]; i += 1
        q, b, l, r = cfg
        mv = p[2*q + b]
        w = int(mv[0]); d = mv[1] == "L"
        x = r if d else l
        j = dfa(d, x, w)
        add_edge(d, j, w, x)
        z = l if d else r
        wait[1-d][z].append((cfg, j))
        for edge in tuple(edges[1-d][z]): pop(cfg, edge, j)
    return (not failure, len(todo), edges, seen, D, tab)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    raw = TABLE.replace("_", "")
    p = [raw[i:i+3] for i in range(0, 36, 3)]
    cert = abstract(p, blockgram(LEFT), blockgram(RIGHT))
    got = (cert[1], len(cert[-1][0]), len(cert[-1][1]))
    assert cert[0] and got == EXPECTED, (cert[0], got)
    source = (
        "import TwoSidedAutomata\n"
        "set_option maxRecDepth 100000\n"
        "set_option maxHeartbeats 0\n"
        "namespace BB6.Agent4Raw56RootE11LB.M39232Block\n"
        "open BB6Coverage\n"
        + emit("39232", p, cert)
        + "\nend BB6.Agent4Raw56RootE11LB.M39232Block\n"
    )
    Path(args.out).write_text(source)
    print(f"M39232 certificate: joint={got[0]} left={got[1]} right={got[2]} bytes={len(source)}")

if __name__ == "__main__":
    main()
